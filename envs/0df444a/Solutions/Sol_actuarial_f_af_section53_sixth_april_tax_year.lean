-- Prove2me | solution 1 for actuarial_f_af_section53_sixth_april_tax_year
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:50:37.889977+00:00
-- url     : https://prove2.me/submissions/e4b8432b-44ba-40bd-a1e8-2d14b3e0fe3b

import Mathlib
import Definitions.Def_actuarial_f_afTaxYearFromYYYYMMDD
open ActuarialUnderpinsF

theorem solution :
    afTaxYearFromYYYYMMDD 20270406 = 2027 := by
  unfold afTaxYearFromYYYYMMDD; norm_num
