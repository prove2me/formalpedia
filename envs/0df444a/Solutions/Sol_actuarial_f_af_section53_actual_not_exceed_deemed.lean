-- Prove2me | solution 1 for actuarial_f_af_section53_actual_not_exceed_deemed
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:59:09.348911+00:00
-- url     : https://prove2.me/submissions/561cfc47-b730-4f92-a617-5bef6be96658

import Mathlib
import Definitions.Def_actuarial_f_afSection53DeemedPension
import Definitions.Def_actuarial_f_afSection53ActualPension
open ActuarialUnderpinsF

theorem solution
    (before required credit : ℝ)
    (hr : 0 ≤ required) (hc : 0 ≤ credit) :
    afSection53ActualPension before required credit ≤
      afSection53DeemedPension before required := by
  unfold afSection53ActualPension afSection53DeemedPension afSection53StillPayable
  have : max 0 (required - credit) ≤ required := max_le hr (by linarith)
  linarith
