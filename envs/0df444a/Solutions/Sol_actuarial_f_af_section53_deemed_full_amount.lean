-- Prove2me | solution 1 for actuarial_f_af_section53_deemed_full_amount
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:53:59.667929+00:00
-- url     : https://prove2.me/submissions/27460170-850b-4a63-ae05-7fea430ef110

import Mathlib
import Definitions.Def_actuarial_f_afSection53DeemedPension
open ActuarialUnderpinsF

theorem solution
    (before required credit : ℝ) :
    afSection53DeemedPension before required =
      before + required := by
  rfl
