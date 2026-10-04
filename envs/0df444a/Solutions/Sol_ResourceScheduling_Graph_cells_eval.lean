-- Prove2me | solution 1 for ResourceScheduling.Graph.cells_eval
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T15:58:53.946709+00:00
-- url     : https://prove2.me/submissions/894679c8-859a-4517-bdf1-08d944a493ae

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram

set_option autoImplicit false
open ResourceScheduling.Graph GraphReg

theorem solution (s : RAMState GraphReg) :
    (GraphProgram.validateCell.eval s).val good =
      (if s.word.getD (s.val i * s.val n + s.val j) Letter.sep = Letter.one ∧
        s.word.getD (s.val j * s.val n + s.val i) Letter.sep ≠ Letter.one then 0 else s.val good) ∧
    ((GraphProgram.ifNonEdge (.inc count)).eval s).val count = s.val count +
      (if s.val i < s.val j ∧ s.word.getD (s.val i * s.val n + s.val j) Letter.sep ≠ Letter.one
        then 1 else 0) ∧
    (GraphProgram.emitCell.eval s).out =
      (unary (if s.val k = s.val i ∨ s.val k = s.val j then 1 else 0)).reverse ++ s.out := by
  constructor
  · simp [GraphProgram.validateCell, GraphProgram.read, GraphProgram.block, RAMCode.eval,
      RAMState.set, Nat.add_comm]
    split_ifs <;> simp_all [Nat.add_comm]
  constructor
  · simp [GraphProgram.ifNonEdge, GraphProgram.read, GraphProgram.block, RAMCode.eval,
      RAMState.set, Nat.add_comm, Nat.sub_pos_iff_lt]
    split_ifs <;> simp_all [Nat.add_comm]
  · simp [GraphProgram.emitCell, GraphProgram.ifEq, GraphProgram.block, RAMCode.eval,
      RAMState.set, unary, Nat.sub_pos_iff_lt]
    split_ifs <;> simp_all <;> omega

#print axioms solution
