-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_fixed_component_error
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:54:07.324175+00:00
-- url     : https://prove2.me/submissions/840c3f3d-d621-4433-8de9-4a6c4c76aa02

import Definitions.Def_TaoFivePrimes_RHDirect132FastNumerator
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Finset

namespace Direct132FastNumeratorProof

lemma fast_choose_eq (n m : ℕ) : RHNextMomentInteger.fastChoose n m=Nat.choose n m := by
  by_cases h : m≤n
  · simp only [RHNextMomentInteger.fastChoose,if_pos h,Nat.choose_eq_factorial_div_factorial h]
  · simp only [RHNextMomentInteger.fastChoose,if_neg h,Nat.choose_eq_zero_of_lt (lt_of_not_ge h)]

lemma weight_eq (i k m : ℕ) :
    RHDirect132FastNumerator.weight i k m = RHDirect132CachedRule.weight i k m := by
  simp only [RHDirect132FastNumerator.weight,RHDirect132CachedRule.weight,fast_choose_eq]

lemma panelRe_eq (i k : ℕ) :
    RHDirect132FastNumerator.panelRe i k = RHDirect132CachedRule.panelRe i k := by
  unfold RHDirect132FastNumerator.panelRe RHDirect132CachedRule.panelRe
  simp_rw [weight_eq]

lemma panelIm_eq (i k : ℕ) :
    RHDirect132FastNumerator.panelIm i k = RHDirect132CachedRule.panelIm i k := by
  unfold RHDirect132FastNumerator.panelIm RHDirect132CachedRule.panelIm
  simp_rw [weight_eq]

lemma numeratorRe_eq (k : ℕ) :
    RHDirect132FastNumerator.numeratorRe k = RHDirect132CachedRule.numeratorRe k := by
  unfold RHDirect132FastNumerator.numeratorRe RHDirect132CachedRule.numeratorRe
  simp_rw [panelRe_eq,panelIm_eq]

lemma numeratorIm_eq (k : ℕ) :
    RHDirect132FastNumerator.numeratorIm k = RHDirect132CachedRule.numeratorIm k := by
  unfold RHDirect132FastNumerator.numeratorIm RHDirect132CachedRule.numeratorIm
  simp_rw [panelRe_eq,panelIm_eq]

end Direct132FastNumeratorProof


namespace Direct132FixedTransfer

noncomputable def component (k : ℕ) : ℝ :=
  if k%2=0 then (RHDirect132CachedRule.value k).re else (RHDirect132CachedRule.value k).im

noncomputable def proposed (k : ℕ) : ℝ := (RHDirect132FastNumerator.fixed k:ℝ)/10^90

lemma denominator_pos (k : ℕ) : 0 < (RHDirect132CachedRule.denominator k:ℝ) := by
  have hw : 0<RHNextMomentInteger.weightDenominator := by
    unfold RHNextMomentInteger.weightDenominator RH14MomentEnclosureProof.CertifiedMomentWeights.denominator
    decide
  have hs : 0<CertifiedFixedPoint.scale310 := by
    unfold CertifiedFixedPoint.scale310
    norm_num
  unfold RHDirect132CachedRule.denominator
  have hf : 0<k.factorial := Nat.factorial_pos k
  positivity

lemma value_re (k : ℕ) :
    (RHDirect132CachedRule.value k).re =
      (3:ℝ)^(k+1)*(RHDirect132CachedRule.numeratorRe k:ℝ)/
        (RHDirect132CachedRule.denominator k:ℝ) := by
  unfold RHDirect132CachedRule.value
  rw [Complex.div_natCast_re]
  have hpow : (3:ℂ)^(k+1) = (((3:ℝ)^(k+1):ℝ):ℂ) := by push_cast; rfl
  have hre : ((3:ℂ)^(k+1)).re=(3:ℝ)^(k+1) := by rw [hpow]; rfl
  have him : ((3:ℂ)^(k+1)).im=0 := by rw [hpow]; rfl
  simp [Complex.mul_re,hre,him]

lemma value_im (k : ℕ) :
    (RHDirect132CachedRule.value k).im =
      (3:ℝ)^(k+1)*(RHDirect132CachedRule.numeratorIm k:ℝ)/
        (RHDirect132CachedRule.denominator k:ℝ) := by
  unfold RHDirect132CachedRule.value
  rw [Complex.div_natCast_im]
  have hpow : (3:ℂ)^(k+1) = (((3:ℝ)^(k+1):ℝ):ℂ) := by push_cast; rfl
  have hre : ((3:ℂ)^(k+1)).re=(3:ℝ)^(k+1) := by rw [hpow]; rfl
  have him : ((3:ℂ)^(k+1)).im=0 := by rw [hpow]; rfl
  simp [Complex.mul_im,hre,him]

lemma component_eq (k : ℕ) :
    component k = (3:ℝ)^(k+1)*(RHDirect132FastNumerator.component k:ℝ)/
      (RHDirect132CachedRule.denominator k:ℝ) := by
  by_cases h : k%2=0
  · simp [component,RHDirect132FastNumerator.component,h,
      Direct132FastNumeratorProof.numeratorRe_eq,value_re]
  · simp [component,RHDirect132FastNumerator.component,h,
      Direct132FastNumeratorProof.numeratorIm_eq,value_im]

lemma fixed_error (k : ℕ) (hfloor : RHDirect132FastNumerator.floorHolds k) :
    |component k-proposed k| ≤ 1/10^90 := by
  have hd := denominator_pos k
  have hs : (0:ℝ)<10^90 := by positivity
  rcases hfloor with ⟨hl,hu⟩
  have hl' : (RHDirect132FastNumerator.fixed k:ℝ)*
      (RHDirect132CachedRule.denominator k:ℝ) ≤
      (10^90:ℝ)*(3:ℝ)^(k+1)*(RHDirect132FastNumerator.component k:ℝ) := by
    exact_mod_cast hl
  have hu' : (10^90:ℝ)*(3:ℝ)^(k+1)*(RHDirect132FastNumerator.component k:ℝ) <
      ((RHDirect132FastNumerator.fixed k:ℝ)+1)*
        (RHDirect132CachedRule.denominator k:ℝ) := by
    exact_mod_cast hu
  have hlow : proposed k ≤ component k := by
    rw [proposed,component_eq]
    apply (div_le_div_iff₀ hs hd).2
    nlinarith only [hl']
  have hupp : component k < ((RHDirect132FastNumerator.fixed k:ℝ)+1)/10^90 := by
    rw [component_eq]
    apply (div_lt_div_iff₀ hd hs).2
    nlinarith only [hu']
  rw [abs_le]
  constructor <;> unfold proposed at * <;> linarith

end Direct132FixedTransfer

theorem solution (k : ℕ) (hfloor : RHDirect132FastNumerator.floorHolds k) :
    |(if k%2=0 then (RHDirect132CachedRule.value k).re else (RHDirect132CachedRule.value k).im) -
      (RHDirect132FastNumerator.fixed k:ℝ)/10^90| ≤ 1/10^90 := by
  simpa only [Direct132FixedTransfer.component,Direct132FixedTransfer.proposed] using
    Direct132FixedTransfer.fixed_error k hfloor
