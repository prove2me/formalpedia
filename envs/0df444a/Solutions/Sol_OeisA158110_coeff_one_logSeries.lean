-- Prove2me | solution 1 for OeisA158110.coeff_one_logSeries
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-27T06:26:52.259628+00:00
-- url     : https://prove2.me/submissions/92a53e8a-76fc-4f95-b6fe-b522214fef42

import Mathlib
import Definitions.Def_OeisA158110_Series
set_option autoImplicit false
open PowerSeries
open OeisA158110 (logSeries)

/-!
Coefficient of $x$ in `logSeries 2 3`:
$[x^1] L = 2^{1^3}/1 = 2$.
-/

theorem solution : coeff 1 (logSeries 2 3) = 2 := by
  simp [logSeries, coeff_mk]
