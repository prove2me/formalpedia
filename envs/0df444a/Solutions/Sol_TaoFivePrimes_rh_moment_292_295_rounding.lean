-- Prove2me | solution 1 for TaoFivePrimes.rh_moment_292_295_rounding
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:59:05.718069+00:00
-- url     : https://prove2.me/submissions/769e1d6d-5d52-45e7-be8b-9553e65b9d4b

import Mathlib.Tactic
import Theorems.Thm_TaoFivePrimes_rh_moment_292_293_rounding
import Theorems.Thm_TaoFivePrimes_rh_moment_294_295_rounding

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : ∀ n : Fin 4,
    let j := 272+20+n.val
    let c := TaoFivePrimes_RHExtendedMomentData272to303.getD (20+n.val) 0
    c*(RHNextMomentInteger.denominator j:ℤ) ≤ 3*(10^64:ℤ)*RHNextMomentCached.numerator j ∧
    3*(10^64:ℤ)*RHNextMomentCached.numerator j < (c+1)*(RHNextMomentInteger.denominator j:ℤ) := by
  intro n
  fin_cases n
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh_moment_292_293_rounding (⟨0,by norm_num⟩:Fin 2)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh_moment_292_293_rounding (⟨1,by norm_num⟩:Fin 2)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh_moment_294_295_rounding (⟨0,by norm_num⟩:Fin 2)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh_moment_294_295_rounding (⟨1,by norm_num⟩:Fin 2)
