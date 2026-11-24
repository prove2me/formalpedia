-- Prove2me | solution 2 for ValueAwareRR.normalizationScale_pos
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-24T09:04:37.502798+00:00
-- url     : https://prove2.me/submissions/2e33742f-fc70-4e1d-9a6a-c087a54cb4be

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.normalizationScale_pos (m : ℚ) (hm : 2 ≤ m) : 0 < normalizationScale m := by
  unfold normalizationScale familyA
  have h : (0:ℚ) < 3 * m - 1 := by linarith
  positivity


theorem solution (m : ℚ) (hm : 2 ≤ m) : 0 < normalizationScale m := by
  unfold normalizationScale familyA
  have h : (0:ℚ) < 3 * m - 1 := by linarith
  positivity
