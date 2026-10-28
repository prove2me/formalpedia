-- Prove2me | solution 1 for TaoFivePrimes.rh_moment_286_287_rounding
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T20:01:48.780984+00:00
-- url     : https://prove2.me/submissions/271c4ada-7423-4616-a00c-988594c386c0

import Mathlib.Tactic
import Theorems.Thm_TaoFivePrimes_rh_moment_284_287_rounding
set_option autoImplicit false
set_option maxRecDepth 100000
theorem solution : ∀ n : Fin 2,
    let j := 272+14+n.val
    let c := TaoFivePrimes_RHExtendedMomentData272to303.getD (14+n.val) 0
    c*(RHNextMomentInteger.denominator j:ℤ) ≤ 3*(10^64:ℤ)*RHNextMomentCached.numerator j ∧
    3*(10^64:ℤ)*RHNextMomentCached.numerator j < (c+1)*(RHNextMomentInteger.denominator j:ℤ) := by
  intro n
  fin_cases n
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh_moment_284_287_rounding (⟨2,by norm_num⟩:Fin 4)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh_moment_284_287_rounding (⟨3,by norm_num⟩:Fin 4)
