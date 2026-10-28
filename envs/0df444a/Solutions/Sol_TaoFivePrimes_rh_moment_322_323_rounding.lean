-- Prove2me | solution 1 for TaoFivePrimes.rh_moment_322_323_rounding
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:05:39.54031+00:00
-- url     : https://prove2.me/submissions/716a4bfe-e836-4d8f-9854-52164f32114d

import Definitions.Def_TaoFivePrimes_RHExtendedMomentData320to335
import Definitions.Def_TaoFivePrimes_RHExtendedMomentCachedNumerator
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ n : Fin 2,
    let j := 320+2+n.val
    let c := TaoFivePrimes_RHExtendedMomentData320to335.getD (2+n.val) 0
    c*(RHNextMomentInteger.denominator j:ℤ) ≤ 3*(10^64:ℤ)*RHNextMomentCached.numerator j ∧
    3*(10^64:ℤ)*RHNextMomentCached.numerator j < (c+1)*(RHNextMomentInteger.denominator j:ℤ) := by
  intro n
  fin_cases n <;> decide +kernel
