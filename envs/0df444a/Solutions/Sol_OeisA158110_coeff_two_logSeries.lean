-- Prove2me | solution 1 for OeisA158110.coeff_two_logSeries
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-27T06:26:54.515233+00:00
-- url     : https://prove2.me/submissions/53f5b511-dbbf-48fd-914a-e928f2c0e782

import Mathlib
import Definitions.Def_OeisA158110_Series
set_option autoImplicit false
open PowerSeries
open OeisA158110 (logSeries)

/-!
Coefficient of $x^2$ in `logSeries 2 3`:
$[x^2] L = 2^{2^3}/2 = 2^8/2 = 256/2 = 128$.
-/

theorem solution : coeff 2 (logSeries 2 3) = 128 := by
  simp [logSeries, coeff_mk]
  norm_num
