-- Prove2me | solution 4 for PiIrrationality.rhin_viola_bound
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T09:30:15.50197+00:00
-- url     : https://prove2.me/submissions/089ac5e0-f00c-48c5-94ef-76a65815d710

import Definitions.Def_PiIrrationality_UpperBound
import Theorems.Thm_PiIrrationality_ZZEven_upperBound_of_saving
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

theorem solution : PiIrrationality.UpperBound (14.797074 : ℝ) := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  have hlam : (∑ k ∈ Finset.range 0, ((4 : ℝ) / (2 * k + 1) - 6 / (3 * k + 2))) = (0 : ℝ) := by
    norm_num [Finset.sum_range_succ]
  have hδ : (0 : ℝ) < 1 / 1000 := by norm_num
  have ht : (0 : ℝ) < 5 * Real.log 2 - 1 - 10 * (1 / 1000) + (0 : ℝ) := by norm_num at h1 ⊢; linarith
  have hg : (0 : ℝ) < 5 * Real.log 2 - 102 / 100 - 11 * (1 / 1000) + (0 : ℝ) := by
    norm_num at h1 ⊢; linarith
  apply PiIrrationality.ZZEven.upperBound_of_saving 0 (1 / 1000) 14.797074 hδ
  · rw [hlam]; norm_num at h2 ⊢; linarith
  · rw [hlam]; exact hg
  · rw [hlam]
    have : (2522 / 100 + 10 * (1 / 1000) - Real.log 2 - (0 : ℝ)) /
        (5 * Real.log 2 - 1 - 10 * (1 / 1000) + (0 : ℝ)) ≤ 14.797074 - 1 := by
      rw [div_le_iff₀ ht]; norm_num at h1 h2 ⊢; nlinarith
    linarith
  · rw [hlam]
    have : (2522 / 100 + 10 * (1 / 1000) - Real.log 2 - (0 : ℝ)) /
        (5 * Real.log 2 - 102 / 100 - 11 * (1 / 1000) + (0 : ℝ)) ≤ 14.797074 - 1 := by
      rw [div_le_iff₀ hg]; norm_num at h1 h2 ⊢; nlinarith
    linarith
