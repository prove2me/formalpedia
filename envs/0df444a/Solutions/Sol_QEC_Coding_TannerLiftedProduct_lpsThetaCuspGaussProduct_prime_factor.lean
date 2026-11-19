-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_prime_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:53:05.229165+00:00
-- url     : https://prove2.me/submissions/8eb1c80a-e794-4b62-bd99-3340f4a7ce9d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaEisensteinPrimeCuspFactor_of_column
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticEisensteinCuspConstant_of_column
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Gauss_ne_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Gauss_sq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsStandardThetaModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspGaussProduct_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspGaussProduct_prime
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspGaussProduct_prime_pow_ge_two
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
theorem _root_.solution (q v L : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (hc : q.Coprime L) (γ : SL(2,ℤ)) (hC : γ 1 0=((q^v*L:ℕ):ℤ))
    (ha : IsUnit ((γ 0 0 * (L : ℤ) : ℤ) : ZMod (q ^ v))) :
    lpsThetaCuspGaussProduct q (γ 0 0*(L:ℤ)) (q^v)=
      (q:ℂ)^2/((q:ℂ)^2-1)*((q^v:ℕ):ℂ)^2*
        (lpsThetaEisensteinPrimeCuspFactor q γ+lpsQuadraticEisensteinCuspConstant q γ) := by
  have hq2 : q≠2 := by intro h;subst q;norm_num at hq4
  have hq : (q:ℂ)≠0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hqs : (q:ℂ)^2-1≠0 := by
    have hr : (1:ℝ)<(q:ℝ) := by exact_mod_cast (Fact.out : q.Prime).one_lt
    have hs : (q:ℝ)^2-1≠0 := by nlinarith
    exact_mod_cast hs
  have hG := lpsQuadraticE2Gauss_ne_zero q hq2
  rw [lpsThetaEisensteinPrimeCuspFactor_of_column q v L hc γ hC,
    lpsQuadraticEisensteinCuspConstant_of_column q v L hq4 hc γ hC]
  by_cases h0 : v=0
  · subst v
    rw [pow_zero,lpsThetaCuspGaussProduct_one]
    norm_num
    field_simp
  · rw [if_neg h0]
    by_cases h1 : v=1
    · subst v
      have ha' : IsUnit ((γ 0 0 * (L : ℤ) : ℤ) : ZMod q) :=
        Eq.mp (congrArg (fun N => IsUnit ((γ 0 0 * (L : ℤ) : ℤ) : ZMod N)) (pow_one q)) ha
      simp only [pow_one]
      have hn : ((((γ 0 0*(L:ℤ)):ℤ):ZMod q))≠0 := isUnit_iff_ne_zero.mp ha'
      rw [lpsThetaCuspGaussProduct_prime q hq2 _ hn]
      norm_num
      have hs := lpsQuadraticE2Gauss_sq q hq4
      field_simp [hqs,hG]
      rw [hs]
      ring
    · rw [if_neg h1,if_neg h1]
      have hv : 2≤v := by omega
      obtain ⟨e,he⟩ := Nat.exists_eq_add_of_le hv
      have he' : v=e+2 := by omega
      rw [he'] at ha ⊢
      rw [lpsThetaCuspGaussProduct_prime_pow_ge_two q hq2 e _ ha]
      field_simp [hqs]
      ring
end QEC.Coding.TannerLiftedProduct
