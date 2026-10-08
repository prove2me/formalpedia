-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weightedRootComplexToRealBalanceV3
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T09:50:13.123928+00:00
-- url     : https://prove2.me/submissions/d0d72e15-cdaf-4b0f-baf9-6573fc64386b

import Mathlib

theorem solution
    (J S P : ℝ)
    (hcomplex : (2 * (J : ℂ)) * Complex.I =
      2 * Real.pi * Complex.I * ((S - P : ℝ) : ℂ)) :
    2 * J = 2 * Real.pi * (S - P) := by
  have him := congrArg Complex.im hcomplex
  simpa using him
