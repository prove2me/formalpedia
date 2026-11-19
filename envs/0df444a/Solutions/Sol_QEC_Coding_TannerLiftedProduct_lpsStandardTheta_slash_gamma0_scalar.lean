-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsStandardTheta_slash_gamma0_scalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:30:05.515853+00:00
-- url     : https://prove2.me/submissions/ea648ac9-8edf-4373-9993-7c1b80783ea9

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaGaussScalar
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsStandardTheta_slash_level_scalar
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0_pos_lower_dvd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsStandardTheta_slash_neg_matrix
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsStandardTheta_slash_zero_c
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real
open scoped UpperHalfPlane ModularForm MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) (hq : 0 < q) (γ : SL(2,ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 (16*q^2)) (z : UpperHalfPlane) :
    ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2:ℤ)] γ) z =
      lpsThetaGammaGaussScalar q γ * lpsStandardTheta q z := by
  rcases lt_trichotomy (γ 1 0) 0 with hn | hz | hp
  · have hpos : 0 < (-γ) 1 0 := by simpa using neg_pos.mpr hn
    have hγn : (-γ) ∈ CongruenceSubgroup.Gamma0 (16*q^2) := by
      rw [CongruenceSubgroup.Gamma0_mem] at hγ ⊢
      simpa using congrArg Neg.neg hγ
    have h := lpsStandardTheta_slash_level_scalar q hq (-γ) hpos
      (lpsGamma0_pos_lower_dvd _ _ hγn hpos) z
    rw [lpsStandardTheta_slash_neg_matrix] at h
    simpa only [lpsThetaGammaGaussScalar,if_neg (ne_of_lt hn),if_neg (not_lt_of_ge hn.le),
      lpsThetaPositiveGaussScalar] using h
  · have h := congrArg (fun f : UpperHalfPlane → ℂ => f z) (lpsStandardTheta_slash_zero_c q γ hz)
    simpa only [lpsThetaGammaGaussScalar,if_pos hz,one_mul] using h
  · have h := lpsStandardTheta_slash_level_scalar q hq γ hp
      (lpsGamma0_pos_lower_dvd _ _ hγ hp) z
    simpa only [lpsThetaGammaGaussScalar,if_neg (ne_of_gt hp),if_pos hp,
      lpsThetaPositiveGaussScalar] using h
end QEC.Coding.TannerLiftedProduct
