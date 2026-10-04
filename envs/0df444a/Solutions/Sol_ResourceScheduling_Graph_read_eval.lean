-- Prove2me | solution 1 for ResourceScheduling.Graph.read_eval
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T15:58:53.218865+00:00
-- url     : https://prove2.me/submissions/8a86c647-f442-4c88-b2fe-ed6c11e0cb3a

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram

set_option autoImplicit false
open ResourceScheduling.Graph GraphReg

theorem solution (a b dst : GraphReg) (h : b ≠ index) (s : RAMState GraphReg) :
    (GraphProgram.read a b dst h).eval s =
      let z := s.val a * s.val n + s.val b
      (s.set index z).set dst (if s.word.getD z Letter.sep = Letter.one then 1 else 0) := by
  simp [GraphProgram.read, GraphProgram.block, RAMCode.eval, RAMState.set, h, Nat.add_comm]

#print axioms solution
