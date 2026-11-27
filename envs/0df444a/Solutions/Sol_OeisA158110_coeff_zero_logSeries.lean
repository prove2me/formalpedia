-- Prove2me | solution 1 for OeisA158110.coeff_zero_logSeries
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-27T06:09:41.020408+00:00
-- url     : https://prove2.me/submissions/8c37ac8b-922a-49f0-8eb3-f0d0aaccab90

import Mathlib
import Definitions.Def_OeisA158110_Series
set_option autoImplicit false
open PowerSeries
open OeisA158110 (logSeries)

/-!
Direct evaluation of the constant coefficient of `logSeries 2 3`.

By definition,
`logSeries q m = PowerSeries.mk (fun n => if n = 0 then 0 else (q : ℚ) ^ (n ^ m) / n)`,
so `coeff 0 (logSeries 2 3)` is the `n = 0` branch and equals `0`.
-/

theorem solution : coeff 0 (logSeries 2 3) = 0 := by
  simp [logSeries, coeff_mk]
