-- Prove2me | solution 1 for ResourceScheduling.Graph.program_valid
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T15:57:33.419705+00:00
-- url     : https://prove2.me/submissions/c48dace3-f8ba-47f9-bc62-ee32357f4b4d

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram

set_option autoImplicit false
open ResourceScheduling.Graph

theorem solution : GraphProgram.program.Valid := by
  simp [GraphProgram.program, GraphProgram.prepare, GraphProgram.validate,
    GraphProgram.validateRow, GraphProgram.validateCell, GraphProgram.countEdges,
    GraphProgram.emit, GraphProgram.emitRows, GraphProgram.emitCell, GraphProgram.ifNonEdge,
    GraphProgram.ifEq, GraphProgram.read, GraphProgram.forN, GraphProgram.block,
    RAMCode.Valid, RAMCode.writes]

#print axioms solution
