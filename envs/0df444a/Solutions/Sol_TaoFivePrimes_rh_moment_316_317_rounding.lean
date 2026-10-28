-- Prove2me | solution 1 for TaoFivePrimes.rh_moment_316_317_rounding
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:32:53.235254+00:00
-- url     : https://prove2.me/submissions/62b5ca49-8b62-46bc-8407-50b324632bef

import Definitions.Def_TaoFivePrimes_RHExtendedMomentData304to319
import Definitions.Def_TaoFivePrimes_RHExtendedMomentCachedNumerator
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ n : Fin 2,
    let j := 304+12+n.val
    let c := TaoFivePrimes_RHExtendedMomentData304to319.getD (12+n.val) 0
    c*(RHNextMomentInteger.denominator j:ℤ) ≤ 3*(10^64:ℤ)*RHNextMomentCached.numerator j ∧
    3*(10^64:ℤ)*RHNextMomentCached.numerator j < (c+1)*(RHNextMomentInteger.denominator j:ℤ) := by
  intro n
  fin_cases n <;> decide +kernel
