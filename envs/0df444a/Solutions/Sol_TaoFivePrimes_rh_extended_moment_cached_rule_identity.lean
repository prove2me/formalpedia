-- Prove2me | solution 1 for TaoFivePrimes.rh_extended_moment_cached_rule_identity
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:13:44.005138+00:00
-- url     : https://prove2.me/submissions/548543aa-e311-4dae-ad39-4b4ae925ef1a

import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_RHExtendedMomentCachedNumerator
import Theorems.Thm_TaoFivePrimes_rh_extended_moment_correlations_0
import Theorems.Thm_TaoFivePrimes_rh_extended_moment_correlations_1
import Theorems.Thm_TaoFivePrimes_rh_extended_moment_correlations_2
import Theorems.Thm_TaoFivePrimes_rh_extended_moment_correlations_3

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Finset

private lemma cache_correct (i m : ℕ) (hi : i<16) (hm : m<184) :
    RHNextMomentInteger.correlation i m=TaoFivePrimes_RHExtendedMomentCorrelationCache i m := by
  interval_cases i <;> first
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_0 (⟨0,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_0 (⟨1,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_0 (⟨2,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_0 (⟨3,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_1 (⟨0,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_1 (⟨1,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_1 (⟨2,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_1 (⟨3,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_2 (⟨0,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_2 (⟨1,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_2 (⟨2,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_2 (⟨3,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_3 (⟨0,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_3 (⟨1,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_3 (⟨2,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_3 (⟨3,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)

private lemma numerator_eq (j : ℕ) :
    RHNextMomentInteger.numerator j=RHNextMomentCached.numerator j := by
  unfold RHNextMomentInteger.numerator RHNextMomentCached.numerator
  apply sum_congr rfl
  intro i hi
  unfold RHNextMomentInteger.panelNumerator RHNextMomentCached.panelNumerator
  apply sum_congr rfl
  intro m hm
  by_cases h : m<184
  · simp only [if_pos h]
    rw [cache_correct i m (mem_range.mp hi) h]
  · simp [h]

theorem solution (j : ℕ) :
    TaoFivePrimes_RHExtendedMomentIntegerRule j=TaoFivePrimes_RHExtendedMomentCachedRule j := by
  unfold TaoFivePrimes_RHExtendedMomentIntegerRule TaoFivePrimes_RHExtendedMomentCachedRule
  rw [numerator_eq]
