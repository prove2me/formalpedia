-- Prove2me | solution 1 for QMC0614.exists_ratio_gt_0614
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T01:47:11.013341+00:00
-- url     : https://prove2.me/submissions/c1b51a24-689f-46cb-ac3d-7665442716e2

import Mathlib
import Definitions.Def_QuantumMaxCutBFVProductRounding
import Theorems.Thm_QMC0614_ratio_gt_0614

set_option autoImplicit false
open scoped BigOperators

theorem solution :
    ∃ μ σ : ℝ, 0 ≤ μ ∧ μ ≤ 1 ∧ 0 ≤ σ ∧ σ ≤ 1 ∧
      ∀ s : ℝ, -1 ≤ s → s < 1 / 3 → (0.614 : ℝ) < QMC0614.mixture 1 μ σ s := by
  exact ⟨0.881, 0.28068, by norm_num, by norm_num, by norm_num, by norm_num,
    fun s h1 h2 => QMC0614.ratio_gt_0614 s h1 h2⟩

#print axioms solution
