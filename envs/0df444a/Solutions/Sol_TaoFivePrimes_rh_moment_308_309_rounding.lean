-- Prove2me | solution 1 for TaoFivePrimes.rh_moment_308_309_rounding
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:31:22.390497+00:00
-- url     : https://prove2.me/submissions/db980c28-d1b1-437f-9756-ffbe0b3a400e

import Definitions.Def_TaoFivePrimes_RHExtendedMomentData304to319
import Definitions.Def_TaoFivePrimes_RHExtendedMomentCachedNumerator
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ n : Fin 2,
    let j := 304+4+n.val
    let c := TaoFivePrimes_RHExtendedMomentData304to319.getD (4+n.val) 0
    c*(RHNextMomentInteger.denominator j:ℤ) ≤ 3*(10^64:ℤ)*RHNextMomentCached.numerator j ∧
    3*(10^64:ℤ)*RHNextMomentCached.numerator j < (c+1)*(RHNextMomentInteger.denominator j:ℤ) := by
  intro n
  fin_cases n <;> decide +kernel
