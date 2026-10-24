-- Prove2me | solution 1 for ProjSelfConcordant.ConicExt.pmu_at_inv_kappa
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:03:39.083326+00:00
-- url     : https://prove2.me/submissions/69e06645-cb4d-4fa9-9d9a-b0a2e583763b

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting

open ProjSelfConcordant.ConicExt

theorem solution (κ μ : ℝ) (hκ : 1 ≤ κ) :
    pmu (κ ^ 2 + 1) μ (-κ⁻¹)
        = (2 * (κ ^ 4 + 5 * κ ^ 2 + 2) / κ ^ 3 + μ) * (2 * (κ ^ 2 - 1) / κ - μ) ∧
      pmu (κ ^ 2 + 1) μ κ⁻¹
        = (2 * (κ ^ 4 + 5 * κ ^ 2 + 2) / κ ^ 3 - μ) * (2 * (κ ^ 2 - 1) / κ + μ) := by
  have hκ0 : κ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hκ)
  constructor <;> dsimp [pmu] <;> field_simp [hκ0] <;> ring
