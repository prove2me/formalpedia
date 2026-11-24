-- Prove2me | solution 1 for ValueAwareRR.normalizedResidualMax_scaling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:10:14.106201+00:00
-- url     : https://prove2.me/submissions/5665a5d7-262d-49f5-b115-989f5f250f2b

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_normalizationScale_pos

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (hm : 2 ≤ m) :
    normalizedResidualMax m = normalizationScale m * residualMax m := by
  have hs : 0 ≤ normalizationScale m := (normalizationScale_pos m hm).le
  change max |normalizationScale m * -familyA m|
    (max |normalizationScale m * -familyB m|
      (max |normalizationScale m * familyB m|
        |normalizationScale m * familyA m|)) =
    normalizationScale m *
      max |-familyA m| (max |-familyB m| (max |familyB m| |familyA m|))
  simp only [abs_mul, abs_of_nonneg hs]
  rw [← mul_max_of_nonneg _ _ hs, ← mul_max_of_nonneg _ _ hs,
    ← mul_max_of_nonneg _ _ hs]
end ValueAwareRR
