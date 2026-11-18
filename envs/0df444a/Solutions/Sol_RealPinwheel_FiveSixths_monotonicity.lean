-- Prove2me | solution 1 for RealPinwheel.FiveSixths.monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T09:38:34.389279+00:00
-- url     : https://prove2.me/submissions/dea0df5c-557e-4f91-a829-d33dd0d5000c

import Definitions.Def_RealPinwheel_FiveSixths_Transformations

open RealPinwheel.FiveSixths

theorem solution {n : ℕ} (A : Instance n) (S : ℕ → Fin n)
    (hS : Valid A.period S) (j : Fin n) (b : ℝ) (hb : A.period j ≤ b) :
    Valid (replacePeriod A.period j b) S := by
  classical
  intro i ell hell m
  apply (hS i ell hell m).trans
  apply Finset.card_le_card
  intro t ht
  obtain ⟨ht, hti⟩ := Finset.mem_filter.mp ht
  apply Finset.mem_filter.mpr
  refine ⟨?_, hti⟩
  apply Finset.mem_range.mpr
  apply (Finset.mem_range.mp ht).trans_le
  apply Nat.ceil_mono
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg ell)
  by_cases hij : i = j
  · simpa [hij, replacePeriod] using hb
  · simp [replacePeriod, Function.update_of_ne hij]
