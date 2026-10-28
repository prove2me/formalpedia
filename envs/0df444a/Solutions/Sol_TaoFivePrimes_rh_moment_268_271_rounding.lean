-- Prove2me | solution 1 for TaoFivePrimes.rh_moment_268_271_rounding
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:14:23.036927+00:00
-- url     : https://prove2.me/submissions/1ddf442b-32e3-4faf-a406-7b0fae005cb0

import Definitions.Def_TaoFivePrimes_RHExtendedMomentData256to271
import Definitions.Def_TaoFivePrimes_RHExtendedMomentCachedNumerator
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ n : Fin 4,
    let j := 256+12+n.val
    let c := TaoFivePrimes_RHExtendedMomentData256to271.getD (12+n.val) 0
    c*(RHNextMomentInteger.denominator j:ℤ) ≤ 3*(10^64:ℤ)*RHNextMomentCached.numerator j ∧
    3*(10^64:ℤ)*RHNextMomentCached.numerator j < (c+1)*(RHNextMomentInteger.denominator j:ℤ) := by
  intro n
  fin_cases n <;> decide +kernel
