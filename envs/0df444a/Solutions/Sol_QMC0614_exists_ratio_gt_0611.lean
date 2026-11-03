-- Prove2me | solution 1 for QMC0614.exists_ratio_gt_0611
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T01:47:11.784809+00:00
-- url     : https://prove2.me/submissions/7fb74b03-d6ad-4783-baec-43d7ff4e5252

import Mathlib
import Definitions.Def_QuantumMaxCutBFVProductRounding
import Theorems.Thm_QMC0614_ratio_gt_0611

set_option autoImplicit false
open scoped BigOperators

theorem solution :
    ∃ μ σ : ℝ, 0 ≤ μ ∧ μ ≤ 1 ∧ 0 ≤ σ ∧ σ ≤ 1 ∧
      ∀ s : ℝ, -1 ≤ s → s < 1 / 3 → (0.611 : ℝ) < QMC0614.mixture (14 / 15) μ σ s := by
  exact ⟨0.861, 0.28086, by norm_num, by norm_num, by norm_num, by norm_num,
    fun s h1 h2 => QMC0614.ratio_gt_0611 s h1 h2⟩

#print axioms solution
