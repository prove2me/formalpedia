-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticEisensteinCuspConstant_dilation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:34:31.841123+00:00
-- url     : https://prove2.me/submissions/9424e820-f0c9-4fc1-a07a-c0808b1d846a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinDilation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEisensteinDilationCuspMatrix_column
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEisensteinDilationCuspMatrix_prime_pow_dvd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q m : ℕ) [Fact q.Prime]
    (hm : 0<m) (hmq : m.Coprime q) (γ : SL(2,ℤ)) :
    lpsQuadraticEisensteinCuspConstant q (lpsEisensteinDilationCuspMatrix m hm γ)=
      lpsQuadraticE2Character q (m:ZMod q)*lpsQuadraticEisensteinCuspConstant q γ := by
  let δ := lpsEisensteinDilationCuspMatrix m hm γ
  let d : ℕ := Int.gcd (m:ℤ) (γ 1 0)
  have hcol : (m:ℤ)*γ 0 0=(d:ℤ)*δ 0 0 ∧ γ 1 0=(d:ℤ)*δ 1 0 :=
    lpsEisensteinDilationCuspMatrix_column m hm γ
  have h1 := lpsEisensteinDilationCuspMatrix_prime_pow_dvd q m hm hmq γ 1
  simp only [pow_one] at h1
  have h2 := lpsEisensteinDilationCuspMatrix_prime_pow_dvd q m hm hmq γ 2
  change (q:ℤ)∣γ 1 0 ↔ (q:ℤ)∣δ 1 0 at h1
  change (q:ℤ)^2∣γ 1 0 ↔ (q:ℤ)^2∣δ 1 0 at h2
  change lpsQuadraticEisensteinCuspConstant q δ=_
  unfold lpsQuadraticEisensteinCuspConstant
  by_cases hC : (q:ℤ)∣γ 1 0
  · rw [if_pos hC,if_pos (h1.mp hC)]
    by_cases hC2 : (q:ℤ)^2∣γ 1 0
    · rw [if_pos hC2,if_pos (h2.mp hC2),mul_zero]
    · rw [if_neg hC2,if_neg (fun h => hC2 (h2.mpr h))]
      have hδC := h1.mp hC
      have hq : (q:ℤ)≠0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
      have hD : ((γ 1 0/(q:ℤ):ℤ):ZMod q)≠0 := by
        intro hz
        have hDq := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hz
        have hh : (q:ℤ)^2∣(q:ℤ)*(γ 1 0/(q:ℤ)) := by
          rw [pow_two,mul_dvd_mul_iff_left hq];exact hDq
        rw [Int.mul_ediv_cancel_of_dvd hC] at hh
        exact hC2 hh
      have hδD : ((δ 1 0/(q:ℤ):ℤ):ZMod q)≠0 := by
        intro hz
        have hDq := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hz
        have hh : (q:ℤ)^2∣(q:ℤ)*(δ 1 0/(q:ℤ)) := by
          rw [pow_two,mul_dvd_mul_iff_left hq];exact hDq
        rw [Int.mul_ediv_cancel_of_dvd hδC] at hh
        exact hC2 (h2.mpr hh)
      have hDD : γ 1 0/(q:ℤ)=(d:ℤ)*(δ 1 0/(q:ℤ)) := by
        calc
          γ 1 0/(q:ℤ)=((d:ℤ)*δ 1 0)/(q:ℤ) := congrArg (·/(q:ℤ)) hcol.2
          _=(d:ℤ)*(δ 1 0/(q:ℤ)) := Int.mul_ediv_assoc _ hδC
      have hAF : (m:ZMod q)*(γ 0 0:ZMod q)=(d:ZMod q)*(δ 0 0:ZMod q) := by
        have h := congrArg (fun x : ℤ => (x:ZMod q)) hcol.1
        simpa only [Int.cast_mul,Int.cast_natCast] using h
      have hDF : ((γ 1 0/(q:ℤ):ℤ):ZMod q)=
          (d:ZMod q)*((δ 1 0/(q:ℤ):ℤ):ZMod q) := by
        have h := congrArg (fun x : ℤ => (x:ZMod q)) hDD
        simpa only [Int.cast_mul,Int.cast_natCast] using h
      have hx : (δ 0 0:ZMod q)*((γ 1 0/(q:ℤ):ℤ):ZMod q)=
          (m:ZMod q)*(γ 0 0:ZMod q)*((δ 1 0/(q:ℤ):ℤ):ZMod q) := by
        rw [hDF,hAF];ring
      have he : -(δ 0 0:ZMod q)/((δ 1 0/(q:ℤ):ℤ):ZMod q)=
          (m:ZMod q)*(-(γ 0 0:ZMod q)/((γ 1 0/(q:ℤ):ℤ):ZMod q)) := by
        field_simp [hD,hδD]
        linear_combination -hx
      rw [he,map_mul]
      ring
  · rw [if_neg hC,if_neg (fun h => hC (h1.mpr h)),mul_zero]
end QEC.Coding.TannerLiftedProduct
