-- Prove2me | solution 1 for actuarial_f_af_section53_only_next_tax_year
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:57:52.638996+00:00
-- url     : https://prove2.me/submissions/0f5e7d75-4f00-4d16-852e-ca3d4075592e

import Mathlib
import Definitions.Def_actuarial_f_afSection53NextYearCredit
open ActuarialUnderpinsF

theorem solution
    (given required : ℕ) (credit : ℝ) (pensionCredit : Bool)
    (h : required ≠ given + 1) :
    afSection53NextYearCredit given required pensionCredit credit = 0 := by
  simp [afSection53NextYearCredit, h]
