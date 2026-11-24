-- Prove2me | solution 1 for ValueAwareRR.normalizedMaxPrefixScore_scaling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:06:34.723881+00:00
-- url     : https://prove2.me/submissions/4ca62957-57b2-4d4d-82e1-4bc4bdb2d6ba

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_normalizationScale_pos
import Theorems.Thm_ValueAwareRR_normalizedPrefixOne_scaling
import Theorems.Thm_ValueAwareRR_normalizedPrefixTwo_scaling
import Theorems.Thm_ValueAwareRR_normalizedPrefixThree_scaling

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution
    (m : ℚ) (hm : 2 ≤ m) (o : SignedOrder) :
    normalizedMaxPrefixScore m o = normalizationScale m * maxPrefixScore m o := by
  have hs : 0 ≤ normalizationScale m := (normalizationScale_pos m hm).le
  rw [normalizedMaxPrefixScore, normalizedPrefixOne_scaling,
    normalizedPrefixTwo_scaling, normalizedPrefixThree_scaling, maxPrefixScore]
  simp only [abs_mul, abs_of_nonneg hs]
  rw [← mul_max_of_nonneg _ _ hs, ← mul_max_of_nonneg _ _ hs]
end ValueAwareRR
