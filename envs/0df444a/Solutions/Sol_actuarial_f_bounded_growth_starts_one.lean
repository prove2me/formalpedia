-- Prove2me | solution 1 for actuarial_f_bounded_growth_starts_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:57:22.826478+00:00
-- url     : https://prove2.me/submissions/9c07f4e4-97e0-449d-9390-47888d418576

import Mathlib
import Definitions.Def_actuarial_f_gmpDateYear
import Definitions.Def_actuarial_f_gmpBoundedPost88Growth
open ActuarialUnderpinsF

theorem solution
    (gpd date : ℕ) (q : ℕ → ℝ)
    (h : gmpDateYear date < gmpDateYear gpd) :
    gmpBoundedPost88Growth gpd date q = 1 := by
  have h1 : gmpDateYear date + 1 - gmpDateYear gpd = 0 := by omega
  simp [gmpBoundedPost88Growth, h1]
