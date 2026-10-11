-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Even.mixed_root_certificate
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T03:18:07.023345+00:00
-- url     : https://prove2.me/submissions/96ea5fc0-c96d-4c28-afc2-34dc0e0cbe7f

import Definitions.Def_RPB108_DNE27MixedEnergy_Even
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108 WeilDefect.RPB108.DNE27Even
theorem solution :
    0 ≤ nativeDualSquare ∧ 0 ≤ highMixedSquare ∧ 0 ≤ mixedUpper ∧
    0 ≤ mixedUpper^2-nativeDualSquare-highMixedSquare ∧
    4*nativeDualSquare*highMixedSquare ≤
      (mixedUpper^2-nativeDualSquare-highMixedSquare)^2 := by
  norm_num [nativeDualSquare, highMixedSquare, mixedUpper, rho,
    rawSourceSquare, highFloor]
