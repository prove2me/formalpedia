-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_twentynine_D27_nonexception_even_order_v1
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T01:07:33.931847+00:00
-- url     : https://prove2.me/submissions/90854157-a7a4-462c-b42e-629d2e5a59ac

import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

private theorem even_order (x : ZMod 53) (hx : x ^ 52 = 1) (hn : x ^ 13 ≠ 1) :
    Even (orderOf x) := by
  have hd := orderOf_dvd_of_pow_eq_one hx
  have hle : orderOf x ≤ 52 := Nat.le_of_dvd (by decide) hd
  by_contra h
  have hc : ∀ n : Fin 53, n.val ∣ 52 → ¬ Even n.val → n.val ∣ 13 := by
    decide +kernel
  have hd13 : orderOf x ∣ 13 := hc ⟨orderOf x, Nat.lt_succ_of_le hle⟩ hd h
  exact hn (orderOf_dvd_iff_pow_eq_one.mp hd13)

theorem solution (q4 : Nat) (hcases : q4 = 31 ∨ q4 = 37 ∨ q4 = 41 ∨ q4 = 43 ∨
    q4 = 53 ∨ q4 = 59 ∨ q4 = 61 ∨ q4 = 67 ∨ q4 = 71 ∨ q4 = 73 ∨
    q4 = 79 ∨ q4 = 83) : Even (orderOf (q4 : ZMod 53)) := by
  let : Fact (1 < 53) := ⟨by decide⟩
  have hzero : Even (orderOf (53 : ZMod 53)) := by
    have hz : (53 : ZMod 53) = 0 := by decide +kernel
    rw [hz, orderOf_zero]
    exact ⟨0, rfl⟩
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
  | exact even_order _ (by decide +kernel) (by decide +kernel)
  | exact hzero

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
