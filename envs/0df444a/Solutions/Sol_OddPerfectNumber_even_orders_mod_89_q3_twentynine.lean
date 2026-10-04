-- Prove2me | solution 1 for OddPerfectNumber.even_orders_mod_89_q3_twentynine
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T01:03:15.201991+00:00
-- url     : https://prove2.me/submissions/7ce52d0f-e587-4084-877c-c6eb8cdabe20

import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

private theorem even_order (x : ZMod 89) (hx : x ^ 88 = 1) (hn : x ^ 11 ≠ 1) :
    Even (orderOf x) := by
  have hd := orderOf_dvd_of_pow_eq_one hx
  have hle : orderOf x ≤ 88 := Nat.le_of_dvd (by decide) hd
  by_contra h
  have hc : ∀ n : Fin 89, n.val ∣ 88 → ¬ Even n.val → n.val ∣ 11 := by
    decide +kernel
  have hd11 : orderOf x ∣ 11 := hc ⟨orderOf x, Nat.lt_succ_of_le hle⟩ hd h
  exact hn (orderOf_dvd_iff_pow_eq_one.mp hd11)

theorem solution : Even (orderOf (3 : ZMod 89)) ∧
    Even (orderOf (5 : ZMod 89)) ∧ Even (orderOf (29 : ZMod 89)) := by
  exact ⟨even_order _ (by decide +kernel) (by decide +kernel),
    even_order _ (by decide +kernel) (by decide +kernel),
    even_order _ (by decide +kernel) (by decide +kernel)⟩

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
