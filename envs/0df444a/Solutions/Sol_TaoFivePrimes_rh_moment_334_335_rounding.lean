-- Prove2me | solution 1 for TaoFivePrimes.rh_moment_334_335_rounding
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:07:56.191976+00:00
-- url     : https://prove2.me/submissions/ee212baf-91b1-493c-997a-f2739352fc02

import Definitions.Def_TaoFivePrimes_RHExtendedMomentData320to335
import Definitions.Def_TaoFivePrimes_RHExtendedMomentCachedNumerator
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ n : Fin 2,
    let j := 320+14+n.val
    let c := TaoFivePrimes_RHExtendedMomentData320to335.getD (14+n.val) 0
    c*(RHNextMomentInteger.denominator j:ℤ) ≤ 3*(10^64:ℤ)*RHNextMomentCached.numerator j ∧
    3*(10^64:ℤ)*RHNextMomentCached.numerator j < (c+1)*(RHNextMomentInteger.denominator j:ℤ) := by
  intro n
  fin_cases n <;> decide +kernel
