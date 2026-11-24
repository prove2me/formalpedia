-- Prove2me | solution 1 for ValueAwareRR.normalizedLossRatio_eq_lossRatio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:14:53.388785+00:00
-- url     : https://prove2.me/submissions/8284af54-7ac4-4557-acc0-b09eafc4a956

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_trueOptimal_loss
import Theorems.Thm_ValueAwareRR_normalizationScale_pos
import Theorems.Thm_ValueAwareRR_normalizedExactLoss_scaling

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (hm : 2 ≤ m) :
    normalizedLossRatio m = lossRatio m := by
  rw [normalizedLossRatio, normalizedExactLoss_scaling, normalizedExactLoss_scaling,
    lossRatio]
  have hs : normalizationScale m ≠ 0 := ne_of_gt (normalizationScale_pos m hm)
  have hl : exactLoss m trueOptimalOrder ≠ 0 := by
    rw [trueOptimal_loss]
    norm_num
  field_simp [hs, hl]
end ValueAwareRR
