-- Prove2me | solution 1 for TaoFivePrimes.rh_moment_284_285_rounding
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T20:01:47.542006+00:00
-- url     : https://prove2.me/submissions/c91b8ffc-6bd8-455d-a16c-8a7f07785e7e

import Mathlib.Tactic
import Theorems.Thm_TaoFivePrimes_rh_moment_284_287_rounding
set_option autoImplicit false
set_option maxRecDepth 100000
theorem solution : ∀ n : Fin 2,
    let j := 272+12+n.val
    let c := TaoFivePrimes_RHExtendedMomentData272to303.getD (12+n.val) 0
    c*(RHNextMomentInteger.denominator j:ℤ) ≤ 3*(10^64:ℤ)*RHNextMomentCached.numerator j ∧
    3*(10^64:ℤ)*RHNextMomentCached.numerator j < (c+1)*(RHNextMomentInteger.denominator j:ℤ) := by
  intro n
  fin_cases n
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh_moment_284_287_rounding (⟨0,by norm_num⟩:Fin 4)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh_moment_284_287_rounding (⟨1,by norm_num⟩:Fin 4)
