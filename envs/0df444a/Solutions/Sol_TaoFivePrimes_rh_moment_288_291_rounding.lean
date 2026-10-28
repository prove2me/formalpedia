-- Prove2me | solution 1 for TaoFivePrimes.rh_moment_288_291_rounding
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:48:44.6175+00:00
-- url     : https://prove2.me/submissions/15c4fae7-bca7-4afc-8310-d906d238a29c

import Definitions.Def_TaoFivePrimes_RHExtendedMomentData272to303
import Definitions.Def_TaoFivePrimes_RHExtendedMomentCachedNumerator
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ n : Fin 4,
    let j := 272+16+n.val
    let c := TaoFivePrimes_RHExtendedMomentData272to303.getD (16+n.val) 0
    c*(RHNextMomentInteger.denominator j:ℤ) ≤ 3*(10^64:ℤ)*RHNextMomentCached.numerator j ∧
    3*(10^64:ℤ)*RHNextMomentCached.numerator j < (c+1)*(RHNextMomentInteger.denominator j:ℤ) := by
  intro n
  fin_cases n <;> decide +kernel
