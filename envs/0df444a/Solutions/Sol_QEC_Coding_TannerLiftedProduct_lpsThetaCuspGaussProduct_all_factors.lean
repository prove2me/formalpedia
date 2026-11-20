-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_all_factors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:02:14.827176+00:00
-- url     : https://prove2.me/submissions/a7822b18-0ea1-4e0a-bb6b-cdf3b3da0dc0

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspModulus_decomposition
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspGaussProduct_split
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspGaussProduct_two_factor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspGaussProduct_prime_factor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSL2Z_firstColumn_unit_modulus
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsStandardThetaModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsZMod_unit_descend
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsStandardThetaModularForm_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q N : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (hN : 0<N) (γ : SL(2,ℤ)) (hC : γ 1 0=(N:ℤ)) :
    lpsThetaCuspGaussProduct q (γ 0 0) N=
      (4/3:ℂ)*(q:ℂ)^2/((q:ℂ)^2-1)*(N:ℂ)^2*
        (lpsThetaEisensteinTwoCuspFactor γ+lpsChi4EisensteinCuspConstant γ)*
        (lpsThetaEisensteinPrimeCuspFactor q γ+lpsQuadraticEisensteinCuspConstant q γ) := by
  have hq2 : q≠2 := by intro h;subst q;norm_num at hq4
  have hqodd := (Fact.out : q.Prime).odd_of_ne_two hq2
  let : NeZero N := ⟨hN.ne'⟩
  have ha := lpsSL2Z_firstColumn_unit_modulus N γ hC
  obtain ⟨t,v,L,hL,hcL,heN⟩ := lpsThetaCuspModulus_decomposition q N hN
  have hL2 : L.Coprime 2 := hcL.coprime_dvd_right (dvd_mul_right _ _)
  have hLq : L.Coprime q := hcL.coprime_dvd_right (dvd_mul_left _ _)
  have h2q : (2:ℕ).Coprime q := hqodd.coprime_two_left
  have hrest2 : Odd (q^v*L) := (hqodd.pow (n:=v)).mul hL2.odd_of_right
  have hrestq : q.Coprime (2^t*L) := (h2q.symm.pow_right t).mul_right hLq.symm
  have hu2 := lpsZMod_unit_descend N (2^t)
    (by rw [heN];exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _) (γ 0 0) ha
  have huq := lpsZMod_unit_descend N (q^v)
    (by rw [heN];exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _) (γ 0 0) ha
  have ha2 : IsUnit ((γ 0 0*((q^v*L:ℕ):ℤ):ℤ):ZMod (2^t)) := by
    have hc : (q^v*L).Coprime (2^t) :=
      ((h2q.symm.pow_left v).mul_left hL2).pow_right t
    simpa only [Int.cast_mul,Int.cast_natCast] using
      hu2.mul ((ZMod.isUnit_iff_coprime (q^v*L) (2^t)).mpr hc)
  have haq : IsUnit ((γ 0 0*((2^t*L:ℕ):ℤ):ℤ):ZMod (q^v)) := by
    simpa only [Int.cast_mul,Int.cast_natCast] using
      huq.mul ((ZMod.isUnit_iff_coprime (2^t*L) (q^v)).mpr (hrestq.symm.pow_right v))
  have hC2 : γ 1 0=((2^t*(q^v*L):ℕ):ℤ) := by rw [hC,heN,mul_assoc]
  have hCq : γ 1 0=((q^v*(2^t*L):ℕ):ℤ) := by rw [hC,heN];push_cast;ring
  rw [heN] at ha ⊢
  rw [lpsThetaCuspGaussProduct_split q t v L hq2 hL hcL _ ha,
    lpsThetaCuspGaussProduct_two_factor q t (q^v*L) hqodd hrest2 γ hC2 ha2,
    lpsThetaCuspGaussProduct_prime_factor q v (2^t*L) hq4 hrestq γ hCq haq]
  push_cast
  ring
end QEC.Coding.TannerLiftedProduct
