-- Prove2me | solution 1 for TaoFivePrimes.rh_moments_336_enclosed_1e55
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:07:25.581262+00:00
-- url     : https://prove2.me/submissions/cb9006c3-1f4d-4999-9917-5b4e7e085173

import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_RHMoments336
import Theorems.Thm_TaoFivePrimes_rh_moments_320_enclosed_1e55
import Theorems.Thm_TaoFivePrimes_rh_extended_moment_rule_enclosure_1e55
import Theorems.Thm_TaoFivePrimes_rh_extended_moment_integer_rule_identity
import Theorems.Thm_TaoFivePrimes_rh_extended_moment_cached_rule_identity
import Theorems.Thm_TaoFivePrimes_rh_moment_320_321_rounding
import Theorems.Thm_TaoFivePrimes_rh_moment_322_323_rounding
import Theorems.Thm_TaoFivePrimes_rh_moment_324_325_rounding
import Theorems.Thm_TaoFivePrimes_rh_moment_326_327_rounding
import Theorems.Thm_TaoFivePrimes_rh_moment_328_329_rounding
import Theorems.Thm_TaoFivePrimes_rh_moment_330_331_rounding
import Theorems.Thm_TaoFivePrimes_rh_moment_332_333_rounding
import Theorems.Thm_TaoFivePrimes_rh_moment_334_335_rounding

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Complex

private lemma rounding_all (j : ℕ) (h0 : 320≤j) (h1 : j<336) :
    let c := TaoFivePrimes_RHExtendedMomentData320to335.getD (j-320) 0
    c*(RHNextMomentInteger.denominator j:ℤ) ≤ 3*(10^64:ℤ)*RHNextMomentCached.numerator j ∧
    3*(10^64:ℤ)*RHNextMomentCached.numerator j < (c+1)*(RHNextMomentInteger.denominator j:ℤ) := by
  interval_cases j
  · simpa using TaoFivePrimes.rh_moment_320_321_rounding (⟨0,by norm_num⟩:Fin 2)
  · simpa using TaoFivePrimes.rh_moment_320_321_rounding (⟨1,by norm_num⟩:Fin 2)
  · simpa using TaoFivePrimes.rh_moment_322_323_rounding (⟨0,by norm_num⟩:Fin 2)
  · simpa using TaoFivePrimes.rh_moment_322_323_rounding (⟨1,by norm_num⟩:Fin 2)
  · simpa using TaoFivePrimes.rh_moment_324_325_rounding (⟨0,by norm_num⟩:Fin 2)
  · simpa using TaoFivePrimes.rh_moment_324_325_rounding (⟨1,by norm_num⟩:Fin 2)
  · simpa using TaoFivePrimes.rh_moment_326_327_rounding (⟨0,by norm_num⟩:Fin 2)
  · simpa using TaoFivePrimes.rh_moment_326_327_rounding (⟨1,by norm_num⟩:Fin 2)
  · simpa using TaoFivePrimes.rh_moment_328_329_rounding (⟨0,by norm_num⟩:Fin 2)
  · simpa using TaoFivePrimes.rh_moment_328_329_rounding (⟨1,by norm_num⟩:Fin 2)
  · simpa using TaoFivePrimes.rh_moment_330_331_rounding (⟨0,by norm_num⟩:Fin 2)
  · simpa using TaoFivePrimes.rh_moment_330_331_rounding (⟨1,by norm_num⟩:Fin 2)
  · simpa using TaoFivePrimes.rh_moment_332_333_rounding (⟨0,by norm_num⟩:Fin 2)
  · simpa using TaoFivePrimes.rh_moment_332_333_rounding (⟨1,by norm_num⟩:Fin 2)
  · simpa using TaoFivePrimes.rh_moment_334_335_rounding (⟨0,by norm_num⟩:Fin 2)
  · simpa using TaoFivePrimes.rh_moment_334_335_rounding (⟨1,by norm_num⟩:Fin 2)

private lemma denominator_pos (j : ℕ) : 0<(RHNextMomentInteger.denominator j:ℝ) := by
  exact_mod_cast (show 0<RHNextMomentInteger.denominator j by
    unfold RHNextMomentInteger.denominator RHNextMomentInteger.weightDenominator
      RH14MomentEnclosureProof.CertifiedMomentWeights.denominator CertifiedFixedPoint.scale310
    positivity)

private lemma rule_rounding (j : ℕ) (h0 : 320≤j) (h1 : j<336) :
    |(TaoFivePrimes_RHExtendedMomentCachedRule j:ℝ)-
      (TaoFivePrimes_RHExtendedMomentData320to335.getD (j-320) 0:ℝ)/(10^64:ℝ)| ≤ 1/10^64 := by
  have h := rounding_all j h0 h1
  dsimp only at h
  let c := TaoFivePrimes_RHExtendedMomentData320to335.getD (j-320) 0
  let D := RHNextMomentInteger.denominator j
  let N := RHNextMomentCached.numerator j
  have hL : (c:ℝ)*(D:ℝ) ≤ 3*(10^64:ℝ)*(N:ℝ) := by exact_mod_cast h.1
  have hU : 3*(10^64:ℝ)*(N:ℝ) < ((c:ℝ)+1)*(D:ℝ) := by exact_mod_cast h.2
  have hD : 0<(D:ℝ) := denominator_pos j
  have low : (c:ℝ)/(10^64:ℝ) ≤ 3*(N:ℝ)/(D:ℝ) := by
    apply (le_div_iff₀ hD).2
    have := hL
    nlinarith only [this]
  have high : 3*(N:ℝ)/(D:ℝ) ≤ (c:ℝ)/(10^64:ℝ)+1/10^64 := by
    apply (div_le_iff₀ hD).2
    have := hU.le
    nlinarith only [this]
  have he : (TaoFivePrimes_RHExtendedMomentCachedRule j:ℝ)=3*(N:ℝ)/(D:ℝ) := by
    simp only [TaoFivePrimes_RHExtendedMomentCachedRule,N,D,Rat.cast_div,Rat.cast_mul,
      Rat.cast_ofNat,Rat.cast_intCast,Rat.cast_natCast]
  rw [he]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem solution (j : ℕ) (hj : j<336) :
    |CertifiedGlobalMoments.moment j-TaoFivePrimes_RHMoments336 j| ≤ 162/10^57 := by
  by_cases h : j<320
  · have hh := TaoFivePrimes.rh_moments_320_enclosed_1e55 j h
    simpa [TaoFivePrimes_RHMoments336,h] using hh
  · have h0 : 320≤j := by omega
    have ha := TaoFivePrimes.rh_extended_moment_rule_enclosure_1e55 j
    rw [TaoFivePrimes.rh_extended_moment_integer_rule_identity,
      TaoFivePrimes.rh_extended_moment_cached_rule_identity] at ha
    have he : (CertifiedGlobalMoments.moment j:ℂ)-(TaoFivePrimes_RHExtendedMomentCachedRule j:ℂ)=
        ((CertifiedGlobalMoments.moment j-(TaoFivePrimes_RHExtendedMomentCachedRule j:ℝ):ℝ):ℂ) := by
      push_cast
      ring
    rw [he,Complex.norm_real,Real.norm_eq_abs] at ha
    have hr := rule_rounding j h0 hj
    rw [TaoFivePrimes_RHMoments336,if_neg h]
    calc
      |CertifiedGlobalMoments.moment j-
          (TaoFivePrimes_RHExtendedMomentData320to335.getD (j-320) 0:ℝ)/(10^64:ℝ)| =
        |(CertifiedGlobalMoments.moment j-(TaoFivePrimes_RHExtendedMomentCachedRule j:ℝ))+
          ((TaoFivePrimes_RHExtendedMomentCachedRule j:ℝ)-
            (TaoFivePrimes_RHExtendedMomentData320to335.getD (j-320) 0:ℝ)/(10^64:ℝ))| := by congr 1; ring
      _ ≤ |CertifiedGlobalMoments.moment j-(TaoFivePrimes_RHExtendedMomentCachedRule j:ℝ)|+
            |(TaoFivePrimes_RHExtendedMomentCachedRule j:ℝ)-
              (TaoFivePrimes_RHExtendedMomentData320to335.getD (j-320) 0:ℝ)/(10^64:ℝ)| := abs_add_le _ _
      _ ≤ 162/10^57 := by linarith
