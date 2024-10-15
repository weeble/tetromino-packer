import itertools
from dataclasses import dataclass
from pysat.formula import CNF
from pysat.solvers import Solver
from typing import Literal, Mapping
from collections.abc import Sequence

type TritId = int
type TetrominoId = Literal['*', 'I', 'O', 'L', 'J', 'S', 'Z', 'T']
type EmptyId = Literal[' ']
type ShapePart = EmptyId | TetrominoId

@dataclass(frozen=True)
class Shape:
    width: int
    height: int
    grid: Sequence[Sequence[ShapePart]]
    def read(self, row: int, col: int) -> ShapePart:
        if 0<=row<self.height and 0<=col<self.width:
            return self.grid[row][col]
        else:
            return ' '

@dataclass(frozen=True)
class Rejected:
    pass

@dataclass(frozen=True)
class Permitted:
    board: Shape


@dataclass(frozen=True)
class Trit:
    id: TritId
    tetromino: TetrominoId
    above: TritId | None
    right: TritId | None
    below: TritId | None
    left: TritId | None

@dataclass(frozen=True)
class TritCollection:
    by_id: Mapping[TritId, Trit]
    by_tetromino: Mapping[TetrominoId, list[Trit]]

    def __len__(self):
        return len(self.by_id)


def pad_tetromino(t) -> Shape:
    t=list(t)
    w=max(len(row) for row in t)
    h=len(t)
    padding=' '*w
    return Shape(width=w, height=h, grid=tuple((row+padding)[:w] for row in t))

def rotate90(s: Shape) -> Shape:
    return Shape(
        width=s.height,
        height=s.width,
        grid=tuple(tuple(row)[::-1] for row in zip(*s.grid))
    )

def rotations(s: Shape) -> list[Shape]:
    s2=rotate90(s)
    s3=rotate90(s2)
    s4=rotate90(s3)
    return list({s,s2,s3,s4})

def extract_tetromino_id(s: Shape) -> TetrominoId:
    tid = [x for row in s.grid for x in row if x != ' '][0]
    # assert isinstance(tid, TetrominoId)
    return tid

TETROMINOES_RAW = '''
*

OO
OO

IIII

 SS
SS

ZZ
 ZZ

LLL
L

JJJ
  J

TTT
 T
'''
TETROMINOES = [
        r
        for key, items in itertools.groupby(TETROMINOES_RAW.splitlines(), key=lambda l:l!='')
        if key
        for r in rotations(pad_tetromino(items))
]
TETROMINOES_BY_LETTER = {
        #key: tuple(ts) for (key, ts) in itertools.groupby(TETROMINOES, key=lambda t:''.join(t.grid).replace(' ','')[0])
        key: tuple(ts) for (key, ts) in itertools.groupby(TETROMINOES, key=extract_tetromino_id)
}



def make_trits(tetrominoes: Mapping[TetrominoId, Sequence[Shape]]) -> TritCollection:
    idcounter=0

    trits_by_id : dict[TritId, Trit] = {}
    trits_by_tetromino : dict[TetrominoId, list[Trit]] = {}

    for tetromino_id, shapes in tetrominoes.items():
        for shape in shapes:
            rowcolids={}
            def getid(row, col):
                nonlocal idcounter
                if (row, col) not in rowcolids:
                    rowcolids[row, col] = idcounter
                    idcounter += 1
                return rowcolids[row, col]
            def get_neighbour(row, col):
                if shape.read(row, col) == ' ':
                    return None
                return getid(row, col)
            for row in range(shape.height):
                for col in range(shape.width):
                    if shape.read(row, col) == ' ':
                        continue
                    trit = Trit(
                            id=getid(row, col),
                            tetromino=tetromino_id,
                            above=get_neighbour(row-1,col),
                            right=get_neighbour(row,col+1),
                            below=get_neighbour(row+1,col),
                            left=get_neighbour(row,col-1)
                        )
                    trits_by_id[trit.id] = trit
                    trits_by_tetromino.setdefault(trit.tetromino, []).append(trit)

    return TritCollection(trits_by_id, trits_by_tetromino)

def trit_is_in_cell_proposition(width, height, trit_count, row, col, trit_id):
    assert 0<=col<width
    assert 0<=row<height
    number = 1 + width*height*trit_id + width*row + col
    r2, c2, t2, p = decode_proposition2(width, height, number)
    assert r2 == row
    assert c2 == col
    assert t2 == trit_id
    assert p == True
    return number


@dataclass
class Proposition:
    row: int
    col: int
    trit: Trit
    positive: bool

def decode_proposition2(width, height, proposition):
    positive = proposition > 0
    proposition = abs(proposition) - 1
    trit_id = proposition // (width*height)
    proposition %= width*height
    row = proposition // width
    proposition %= width
    col = proposition
    return row, col, trit_id, positive

def decode_proposition(width, height, trits, proposition):
    row, col, trit_id, positive = decode_proposition2(width, height, proposition)
    trit = trits.by_id[trit_id]
    return Proposition(row, col, trit, positive)



def try_trit_is_in_cell_proposition(width, height, trit_count, row, col, trit_id):
    if 0<=row<height and 0<=col<width:
        return width*height*trit_id + width*col + row
    return None

def make_all_squares_filled_rules(width, height, trits) -> list[list[int]]:
    return [
        [
            trit_is_in_cell_proposition(width, height, len(trits), row, col, trit_id)
            for trit_id in trits.by_id.keys()
        ]
        for row in range(height)
        for col in range(width)
    ]

def get_other_trits(trit, trits):
    return [trit2 for trit2 in trits.by_id.values() if trit2.id != trit.id]

def make_intact_rules(width, height, col, row, trits, trit) -> list[list[int]]:
    rules = []
    if trit.above != None and row>0:
        rules.append([
            trit_is_in_cell_proposition(width, height, len(trits), row-1, col, trit.above),
            -trit_is_in_cell_proposition(width, height, len(trits), row, col, trit.id)
        ])
    if trit.right != None and col<width-1:
        rules.append([
            trit_is_in_cell_proposition(width, height, len(trits), row, col+1, trit.right),
            -trit_is_in_cell_proposition(width, height, len(trits), row, col, trit.id)
        ])
    if trit.below != None and row<height-1:
        rules.append([
            trit_is_in_cell_proposition(width, height, len(trits), row+1, col, trit.below),
            -trit_is_in_cell_proposition(width, height, len(trits), row, col, trit.id)
        ])
    if trit.left != None and col>0:
        rules.append([
            trit_is_in_cell_proposition(width, height, len(trits), row, col-1, trit.left),
            -trit_is_in_cell_proposition(width, height, len(trits), row, col, trit.id)
        ])
    return rules

def make_distinct_rules(width, height, col, row, trits, trit):
    rules = []
    if trit.above == None and row>0:
        clause = [
            -trit_is_in_cell_proposition(width, height, len(trits), row, col, trit.id)
        ]
        clause.extend([
            trit_is_in_cell_proposition(width, height, len(trits), row-1, col, other.id)
            for other in trits.by_id.values()
            if other.tetromino != trit.tetromino
        ])
        rules.append(clause)
    if trit.right == None and col<width-1:
        clause = [
            -trit_is_in_cell_proposition(width, height, len(trits), row, col, trit.id)
        ]
        clause.extend([
            trit_is_in_cell_proposition(width, height, len(trits), row, col+1, other.id)
            for other in trits.by_id.values()
            if other.tetromino != trit.tetromino
        ])
        rules.append(clause)
    if trit.below == None and row<height-1:
        clause = [
            -trit_is_in_cell_proposition(width, height, len(trits), row, col, trit.id)
        ]
        clause.extend([
            trit_is_in_cell_proposition(width, height, len(trits), row+1, col, other.id)
            for other in trits.by_id.values()
            if other.tetromino != trit.tetromino
        ])
        rules.append(clause)
    if trit.left == None and col>0:
        clause = [
            -trit_is_in_cell_proposition(width, height, len(trits), row, col, trit.id)
        ]
        clause.extend([
            trit_is_in_cell_proposition(width, height, len(trits), row, col-1, other.id)
            for other in trits.by_id.values()
            if other.tetromino != trit.tetromino
        ])
        rules.append(clause)
    return rules

def make_edge_rules(width, height, col, row, trits, trit):
    rules = []
    if trit.above != None and row==0:
        rules.append([
            -trit_is_in_cell_proposition(width, height, len(trits), row, col, trit.id)
        ])
    if trit.right != None and col==width-1:
        rules.append([
            -trit_is_in_cell_proposition(width, height, len(trits), row, col, trit.id)
        ])
    if trit.below != None and row==height-1:
        rules.append([
            -trit_is_in_cell_proposition(width, height, len(trits), row, col, trit.id)
        ])
    if trit.left != None and col==0:
        rules.append([
            -trit_is_in_cell_proposition(width, height, len(trits), row, col, trit.id)
        ])
    return rules

def make_in_bounds_tetrominoes_intact_rules(width, height, trits):
    return [
        rule
        for row in range(height)
        for col in range(width)
        for trit in trits.by_id.values()
        for rule in make_intact_rules(width, height, col, row, trits, trit)
    ]

def make_no_tetrominoes_across_edge_rules(width, height, trits):
    return [
        rule
        for row in range(height)
        for col in range(width)
        for trit in trits.by_id.values()
        for rule in make_edge_rules(width, height, col, row, trits, trit)
    ]

def make_no_collisions_rules(width, height, trits):
    return [
        [
            -trit_is_in_cell_proposition(width, height, len(trits), row, col, hot_trit.id),
            -trit_is_in_cell_proposition(width, height, len(trits), row, col, cold_trit.id)
        ]
        for row in range(height)
        for col in range(width)
        for hot_trit in trits.by_id.values()
        for cold_trit in trits.by_id.values()
        if hot_trit.id != cold_trit.id
    ]
    
def make_no_matching_neighbours_rules(width, height, trits):
    return [
        rule
        for row in range(height)
        for col in range(width)
        for trit in trits.by_id.values()
        for rule in make_distinct_rules(width, height, col, row, trits, trit)
    ]



def make_rules(width: int, height: int, trits: TritCollection):
    rules = []
    rules.extend(make_all_squares_filled_rules(width, height, trits))
    rules.extend(make_in_bounds_tetrominoes_intact_rules(width, height, trits))
    rules.extend(make_no_tetrominoes_across_edge_rules(width, height, trits))
    rules.extend(make_no_collisions_rules(width, height, trits))
    rules.extend(make_no_matching_neighbours_rules(width, height, trits))
    return rules

def reassemble(width, height, propositions):
    raw_grid = [[' '] * width for row in range(height)]
    for p in propositions:
        if p.positive:
            raw_grid[p.row][p.col] = p.trit.tetromino
    grid = [''.join(line) for line in raw_grid]
    for line in grid:
        print(line)


    

print(TETROMINOES_BY_LETTER)
TRITS = make_trits(TETROMINOES_BY_LETTER)
print(TRITS)
WIDTH = 8
HEIGHT = 7
RULES = make_rules(WIDTH,HEIGHT,TRITS)
#print(RULES)



# create a satisfiable CNF formula "(-x1 ∨ x2) ∧ (-x1 ∨ -x2)":
cnf = CNF(from_clauses=RULES)

# create a SAT solver for this formula:
with Solver(bootstrap_with=cnf) as solver:
    # 1.1 call the solver for this formula:
    print('formula is', f'{"s" if solver.solve() else "uns"}atisfiable')

    # 1.2 the formula is satisfiable and so has a model:
    propositions = [decode_proposition(WIDTH,HEIGHT,TRITS,x) for x in solver.get_model()]
    reassemble(WIDTH, HEIGHT, propositions)
    #print('and the model is:', [p for p in [decode_proposition(3,2,TRITS,x) for x in solver.get_model()] if p.positive])

    # 2.1 apply the MiniSat-like assumption interface:
    #print('formula is',
    #    f'{"s" if solver.solve(assumptions=[1, 2]) else "uns"}atisfiable',
    #    'assuming x1 and x2')

    # 2.2 the formula is unsatisfiable,
    # i.e. an unsatisfiable core can be extracted:
    print('and the unsatisfiable core is:', solver.get_core())
