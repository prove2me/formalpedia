-- Prove2me | solution 1 for ResourceScheduling.Graph.prepare_eval
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T16:01:41.217063+00:00
-- url     : https://prove2.me/submissions/b6e27655-02f7-4ce8-afe4-03aa3de56b39

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram

set_option autoImplicit false
open ResourceScheduling.Graph GraphReg GraphProgram

theorem solution (s : RAMState GraphReg) :
    (prepare.eval s).val t = (splitOnes s.word).1 ∧
    (prepare.eval s).val n = 3 * (splitOnes s.word).1 ∧
    (prepare.eval s).word = (splitOnes s.word).2.tail ∧
    (prepare.eval s).out = s.out ∧
    (prepare.eval s).val good =
      if (splitOnes s.word).2 ≠ [] ∧ (splitOnes s.word).2.tail.length =
        (3 * (splitOnes s.word).1) * (3 * (splitOnes s.word).1) then 1 else 0 := by
  have h3 (a : ℕ) : 3 * a = a + (a + a) := by omega
  simp [prepare, block, RAMCode.eval, ramParseState, RAMState.set, h3, Nat.add_assoc]
  split_ifs <;> simp_all <;> omega

#print axioms solution
