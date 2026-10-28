-- Prove2me | solution 1 for actuarial_f_af_section53_fifth_april_tax_year
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:55:47.22136+00:00
-- url     : https://prove2.me/submissions/a2fcf5b2-7018-4a11-92f4-12386592a2af

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_afTaxYearFromYYYYMMDD

open ActuarialUnderpinsF



theorem solution :
    afTaxYearFromYYYYMMDD 20270405 = 2026 := by
  norm_num [afTaxYearFromYYYYMMDD]
