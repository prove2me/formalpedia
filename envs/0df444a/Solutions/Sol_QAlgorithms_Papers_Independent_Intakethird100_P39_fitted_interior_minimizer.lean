-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P39.fitted_interior_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:11:11.687118+00:00
-- url     : https://prove2.me/submissions/5629e14a-c8f1-485c-a985-03cb66947889

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P39

open scoped BigOperators

open QAlgorithms.Papers.Independent.Intakethird100.P39 in
theorem solution (S : ℕ) (hS : 4 ≤ S) :
    ∀ k m : ℕ, 4 ≤ k → 1 ≤ m → k * m = S →
      fittedInteriorCost S 1 ≤ fittedInteriorCost k m := by
  intro k m hk hm hkm
  rcases Nat.lt_or_ge m 2 with h | h
  · have hm1 : m = 1 := by omega
    subst hm1
    have hkS : k = S := by omega
    subst hkS
    exact le_refl _
  · have hS' : (S : ℝ) = (k : ℝ) * m := by
      rw [← hkm]
      push_cast
      ring
    have hk' : (4 : ℝ) ≤ k := by exact_mod_cast hk
    have hm' : (2 : ℝ) ≤ m := by exact_mod_cast h
    unfold fittedInteriorCost
    rw [if_pos rfl, if_neg (by omega : ¬ (m = 1)), hS']
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.mpr hk') (sub_nonneg.mpr hm')]
