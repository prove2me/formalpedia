-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Odd.mixed_root_certificate
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T03:18:46.588004+00:00
-- url     : https://prove2.me/submissions/c91d6bae-5a9a-4daf-b70b-b516c0c3ffca

import Definitions.Def_RPB108_DNE27MixedEnergy_Odd
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108 WeilDefect.RPB108.DNE27Odd
theorem solution :
    0 ≤ nativeDualSquare ∧ 0 ≤ highMixedSquare ∧ 0 ≤ mixedUpper ∧
    0 ≤ mixedUpper^2-nativeDualSquare-highMixedSquare ∧
    4*nativeDualSquare*highMixedSquare ≤
      (mixedUpper^2-nativeDualSquare-highMixedSquare)^2 := by
  norm_num [nativeDualSquare, highMixedSquare, mixedUpper, rho,
    rawSourceSquare, highFloor]
