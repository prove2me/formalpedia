-- Prove2me | solution 1 for OddPerfectNumber.even_orders_mod_113_q4_593_599_601
-- status  : ACCEPTED   (disprove)
-- author  : @Patrick
-- created : 2026-09-18T01:00:14.213638+00:00
-- url     : https://prove2.me/submissions/001aa6f9-dbdb-4557-9b43-8fc9f57d0d8d

import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

theorem solution : ¬ (Even (orderOf (593 : ZMod 113)) ∧
    Even (orderOf (599 : ZMod 113)) ∧ Even (orderOf (601 : ZMod 113))) := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have ho : orderOf (593 : ZMod 113) = 7 := by
    apply orderOf_eq_prime
    · decide +kernel
    · decide +kernel
  intro h
  have he := h.1
  rw [ho] at he
  exact (by decide : ¬ Even (7 : ℕ)) he

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
