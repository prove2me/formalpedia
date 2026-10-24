-- Prove2me | solution 1 for ProjSelfConcordant.ConicExt.pmu_pm_factorization
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:04:25.429535+00:00
-- url     : https://prove2.me/submissions/e6f9b23f-b68c-4233-9908-1c7874aa8722

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting

open ProjSelfConcordant.ConicExt

theorem solution (κ t : ℝ) (hκ : 1 ≤ κ) :
    pmu (κ ^ 2 + 1) (2 * (κ ^ 2 - 1) / κ) t
        = 4 * κ⁻¹ ^ 2 * (κ * t + 1) ^ 2
          * (κ * (t ^ 2 + 2) * (t - 1) ^ 2 + (κ - 1) * ((t ^ 4 + 3 * t ^ 2 + 3) * κ + 1)) ∧
      pmu (κ ^ 2 + 1) (-(2 * (κ ^ 2 - 1) / κ)) t
        = 4 * κ⁻¹ ^ 2 * (κ * t - 1) ^ 2
          * (κ * (t ^ 2 + 2) * (t + 1) ^ 2 + (κ - 1) * ((t ^ 4 + 3 * t ^ 2 + 3) * κ + 1)) ∧
      0 ≤ pmu (κ ^ 2 + 1) (2 * (κ ^ 2 - 1) / κ) t ∧
      0 ≤ pmu (κ ^ 2 + 1) (-(2 * (κ ^ 2 - 1) / κ)) t := by
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hκ0 : κ ≠ 0 := ne_of_gt hκpos
  have hκ1 : 0 ≤ κ - 1 := sub_nonneg.mpr hκ
  have hp :
    pmu (κ ^ 2 + 1) (2 * (κ ^ 2 - 1) / κ) t
        = 4 * κ⁻¹ ^ 2 * (κ * t + 1) ^ 2
          * (κ * (t ^ 2 + 2) * (t - 1) ^ 2 + (κ - 1) * ((t ^ 4 + 3 * t ^ 2 + 3) * κ + 1)) := by
    dsimp [pmu]
    field_simp [hκ0]
    ring
  have hm :
      pmu (κ ^ 2 + 1) (-(2 * (κ ^ 2 - 1) / κ)) t
        = 4 * κ⁻¹ ^ 2 * (κ * t - 1) ^ 2
          * (κ * (t ^ 2 + 2) * (t + 1) ^ 2 + (κ - 1) * ((t ^ 4 + 3 * t ^ 2 + 3) * κ + 1)) := by
    dsimp [pmu]
    field_simp [hκ0]
    ring
  refine ⟨hp, hm, ?_, ?_⟩
  · rw [hp]
    positivity
  · rw [hm]
    positivity
