-- Prove2me | solution 1 for TaoFivePrimes.rh_moments_272_enclosed
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:15:32.952992+00:00
-- url     : https://prove2.me/submissions/ad4c4da4-cc6b-4775-bd4f-91c97ff14ef4

import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_RHMoments272
import Theorems.Thm_TaoFivePrimes_rh14to100_moments_enclosed
import Theorems.Thm_TaoFivePrimes_rh_extended_moment_rule_enclosure
import Theorems.Thm_TaoFivePrimes_rh_extended_moment_integer_rule_identity
import Theorems.Thm_TaoFivePrimes_rh_extended_moment_cached_rule_identity
import Theorems.Thm_TaoFivePrimes_rh_moment_256_259_rounding
import Theorems.Thm_TaoFivePrimes_rh_moment_260_263_rounding
import Theorems.Thm_TaoFivePrimes_rh_moment_264_267_rounding
import Theorems.Thm_TaoFivePrimes_rh_moment_268_271_rounding

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Complex

private lemma rounding_all (j : ℕ) (h0 : 256≤j) (h1 : j<272) :
    let c := TaoFivePrimes_RHExtendedMomentData256to271.getD (j-256) 0
    c*(RHNextMomentInteger.denominator j:ℤ) ≤ 3*(10^64:ℤ)*RHNextMomentCached.numerator j ∧
    3*(10^64:ℤ)*RHNextMomentCached.numerator j < (c+1)*(RHNextMomentInteger.denominator j:ℤ) := by
  interval_cases j
  · simpa using TaoFivePrimes.rh_moment_256_259_rounding (⟨0,by norm_num⟩:Fin 4)
  · simpa using TaoFivePrimes.rh_moment_256_259_rounding (⟨1,by norm_num⟩:Fin 4)
  · simpa using TaoFivePrimes.rh_moment_256_259_rounding (⟨2,by norm_num⟩:Fin 4)
  · simpa using TaoFivePrimes.rh_moment_256_259_rounding (⟨3,by norm_num⟩:Fin 4)
  · simpa using TaoFivePrimes.rh_moment_260_263_rounding (⟨0,by norm_num⟩:Fin 4)
  · simpa using TaoFivePrimes.rh_moment_260_263_rounding (⟨1,by norm_num⟩:Fin 4)
  · simpa using TaoFivePrimes.rh_moment_260_263_rounding (⟨2,by norm_num⟩:Fin 4)
  · simpa using TaoFivePrimes.rh_moment_260_263_rounding (⟨3,by norm_num⟩:Fin 4)
  · simpa using TaoFivePrimes.rh_moment_264_267_rounding (⟨0,by norm_num⟩:Fin 4)
  · simpa using TaoFivePrimes.rh_moment_264_267_rounding (⟨1,by norm_num⟩:Fin 4)
  · simpa using TaoFivePrimes.rh_moment_264_267_rounding (⟨2,by norm_num⟩:Fin 4)
  · simpa using TaoFivePrimes.rh_moment_264_267_rounding (⟨3,by norm_num⟩:Fin 4)
  · simpa using TaoFivePrimes.rh_moment_268_271_rounding (⟨0,by norm_num⟩:Fin 4)
  · simpa using TaoFivePrimes.rh_moment_268_271_rounding (⟨1,by norm_num⟩:Fin 4)
  · simpa using TaoFivePrimes.rh_moment_268_271_rounding (⟨2,by norm_num⟩:Fin 4)
  · simpa using TaoFivePrimes.rh_moment_268_271_rounding (⟨3,by norm_num⟩:Fin 4)

private lemma denominator_pos (j : ℕ) : 0<(RHNextMomentInteger.denominator j:ℝ) := by
  exact_mod_cast (show 0<RHNextMomentInteger.denominator j by
    unfold RHNextMomentInteger.denominator RHNextMomentInteger.weightDenominator
      RH14MomentEnclosureProof.CertifiedMomentWeights.denominator CertifiedFixedPoint.scale310
    positivity)

private lemma rule_rounding (j : ℕ) (h0 : 256≤j) (h1 : j<272) :
    |(TaoFivePrimes_RHExtendedMomentCachedRule j:ℝ)-
      (TaoFivePrimes_RHExtendedMomentData256to271.getD (j-256) 0:ℝ)/(10^64:ℝ)| ≤ 1/10^64 := by
  have h := rounding_all j h0 h1
  dsimp only at h
  let c := TaoFivePrimes_RHExtendedMomentData256to271.getD (j-256) 0
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

theorem solution (j : ℕ) (hj : j<272) :
    |CertifiedGlobalMoments.moment j-TaoFivePrimes_RHMoments272 j| ≤ 2/10^46 := by
  by_cases h : j<256
  · have hh := TaoFivePrimes.rh14to100_moments_enclosed j h
    simpa [TaoFivePrimes_RHMoments272,h] using hh.trans (by norm_num : (1/10^46:ℝ) ≤ 2/10^46)
  · have h0 : 256≤j := by omega
    have ha := TaoFivePrimes.rh_extended_moment_rule_enclosure j
    rw [TaoFivePrimes.rh_extended_moment_integer_rule_identity,
      TaoFivePrimes.rh_extended_moment_cached_rule_identity] at ha
    have he : (CertifiedGlobalMoments.moment j:ℂ)-(TaoFivePrimes_RHExtendedMomentCachedRule j:ℂ)=
        ((CertifiedGlobalMoments.moment j-(TaoFivePrimes_RHExtendedMomentCachedRule j:ℝ):ℝ):ℂ) := by
      push_cast
      ring
    rw [he,Complex.norm_real,Real.norm_eq_abs] at ha
    have hr := rule_rounding j h0 hj
    rw [TaoFivePrimes_RHMoments272,if_neg h]
    calc
      |CertifiedGlobalMoments.moment j-
          (TaoFivePrimes_RHExtendedMomentData256to271.getD (j-256) 0:ℝ)/(10^64:ℝ)| =
        |(CertifiedGlobalMoments.moment j-(TaoFivePrimes_RHExtendedMomentCachedRule j:ℝ))+
          ((TaoFivePrimes_RHExtendedMomentCachedRule j:ℝ)-
            (TaoFivePrimes_RHExtendedMomentData256to271.getD (j-256) 0:ℝ)/(10^64:ℝ))| := by congr 1; ring
      _ ≤ |CertifiedGlobalMoments.moment j-(TaoFivePrimes_RHExtendedMomentCachedRule j:ℝ)|+
            |(TaoFivePrimes_RHExtendedMomentCachedRule j:ℝ)-
              (TaoFivePrimes_RHExtendedMomentData256to271.getD (j-256) 0:ℝ)/(10^64:ℝ)| := abs_add_le _ _
      _ ≤ 2/10^46 := by linarith
