-- Prove2me | solution 1 for TarchaBraids.thm_3_15_right_interp_boundaries_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T12:57:38.350812+00:00
-- url     : https://prove2.me/submissions/9437b4d8-99ea-4881-8761-b53bd18907f2

import Mathlib
import Theorems.Thm_TarchaBraids_thm_3_15_right_interp_u_boundaries_v1
import Theorems.Thm_TarchaBraids_thm_3_15_right_interp_time_boundaries_v1

open BraidsLinksMCG TarchaBraids

theorem solution :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      (∀ q : unitInterval,
        configProj n (rightOuterInterpConfig i j hji 0 q) =
          configProj n (rightBraidConfig n i j (q : ℝ))) ∧
      (∀ (hi2 : (i : ℕ) + 2 < n) (q : unitInterval),
        configProj n (rightOuterInterpConfig i j hji 1 q) =
          configProj n (outerRotateConfig i hi2 (q : ℝ))) ∧
      (∀ u : unitInterval,
        configProj n (rightOuterInterpConfig i j hji u 0) = baseUnordered n) ∧
      (∀ u : unitInterval,
        configProj n (rightOuterInterpConfig i j hji u 1) = baseUnordered n) := by
  intro n i j hji
  have hu := TarchaBraids.thm_3_15_right_interp_u_boundaries_v1 i j hji
  have ht := TarchaBraids.thm_3_15_right_interp_time_boundaries_v1 i j hji
  exact ⟨hu.1, ⟨hu.2, ⟨ht.1, ht.2⟩⟩⟩
