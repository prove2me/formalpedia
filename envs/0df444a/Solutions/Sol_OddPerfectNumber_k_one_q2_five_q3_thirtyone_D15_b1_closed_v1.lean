-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirtyone_D15_b1_closed_v1
-- status  : ACCEPTED   (disprove)
-- author  : @cm_beta
-- created : 2026-09-21T01:07:18.931039+00:00
-- url     : https://prove2.me/submissions/abe0d04b-7c61-4c11-8311-fb85cab7bd06

import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 4096

private theorem order61 : orderOf (3 : ZMod 61) = 10 := by
  apply (orderOf_eq_iff (by decide : 0 < 10)).2
  constructor
  · decide
  · intro m hm hmpos
    interval_cases m <;> first | omega | decide

private theorem order151 : orderOf (3 : ZMod 151) = 50 := by
  apply (orderOf_eq_iff (by decide : 0 < 50)).2
  constructor
  · decide
  · intro m hm hmpos
    interval_cases m <;> first | omega | decide

theorem solution : ¬ (∀ (D q4 : Nat), D = 15 → (q4 = 61 ∨ q4 = 151) →
    orderOf (3 : ZMod 61) = 10 → orderOf (3 : ZMod 151) = 50 → False) := by
  intro h
  exact h 15 61 rfl (Or.inl rfl) order61 order151

#print axioms solution
