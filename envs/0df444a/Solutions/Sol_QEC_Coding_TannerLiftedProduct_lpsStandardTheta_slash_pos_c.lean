-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsStandardTheta_slash_pos_c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:27:35.899192+00:00
-- url     : https://prove2.me/submissions/b9beefbe-a6da-4093-8842-e7ea2d6eac12

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsStandardTheta_mobius_raw
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) (hq : 0<q) (γ : SL(2,ℤ)) (hc : 0<γ 1 0)
    (z : UpperHalfPlane) :
    ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2:ℤ)] γ) z =
      -(32*(q:ℂ)^3*((γ 1 0).toNat:ℂ)^2)⁻¹ *
        lpsThetaGaussSum (γ 0 0) (γ 1 0).toNat ((z+(γ 1 1:ℂ)/(γ 1 0:ℂ))/2) *
        lpsThetaGaussSum (4*(q:ℤ)^2*γ 0 0) (γ 1 0).toNat
          ((z+(γ 1 1:ℂ)/(γ 1 0:ℂ))/(8*(q:ℂ)^2))^3 := by
  let c := (γ 1 0).toNat
  have hcn : 0<c := by omega
  let : NeZero c := ⟨ne_of_gt hcn⟩
  have hci : (c:ℤ)=γ 1 0 := Int.toNat_of_nonneg hc.le
  have hcc : (c:ℂ)=(γ 1 0:ℂ) := by exact_mod_cast hci
  have hd : γ 0 0*γ 1 1-γ 0 1*(c:ℤ)=1 := by
    rw [hci]
    simpa only [Matrix.det_fin_two] using γ.det_coe
  have hm : ((γ • z : UpperHalfPlane):ℂ)=((γ 0 0:ℂ)*z+(γ 0 1:ℂ))/((c:ℂ)*z+(γ 1 1:ℂ)) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [hcc]
  have hD : (c:ℂ)*z+(γ 1 1:ℂ)≠0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.add_im,Complex.mul_im,Complex.natCast_re,Complex.natCast_im,
      Complex.intCast_im,zero_mul,add_zero,Complex.zero_im] at hi
    exact (mul_pos (show 0<(c:ℝ) by exact_mod_cast hcn) z.im_pos).ne' hi
  have qn : (q:ℂ)≠0 := by exact_mod_cast ne_of_gt hq
  have cn : (c:ℂ)≠0 := by exact_mod_cast ne_of_gt hcn
  rw [ModularForm.SL_slash_apply,hm,lpsStandardTheta_mobius_raw q hq (γ 0 0) (γ 0 1) (γ 1 1) c hd z z.im_pos]
  simp only [ModularGroup.denom_apply,zpow_neg,zpow_ofNat]
  rw [← hcc]
  change -( ((z:ℂ)+(γ 1 1:ℂ)/(c:ℂ))^2/(32*(q:ℂ)^3)) *
      lpsThetaGaussSum (γ 0 0) c (((z:ℂ)+(γ 1 1:ℂ)/(c:ℂ))/2) *
      lpsThetaGaussSum (4*(q:ℤ)^2*γ 0 0) c (((z:ℂ)+(γ 1 1:ℂ)/(c:ℂ))/(8*(q:ℂ)^2))^3 *
      (((c:ℂ)*(z:ℂ)+(γ 1 1:ℂ))^2)⁻¹ =
      -(32*(q:ℂ)^3*(c:ℂ)^2)⁻¹ *
        lpsThetaGaussSum (γ 0 0) c (((z:ℂ)+(γ 1 1:ℂ)/(c:ℂ))/2) *
        lpsThetaGaussSum (4*(q:ℤ)^2*γ 0 0) c (((z:ℂ)+(γ 1 1:ℂ)/(c:ℂ))/(8*(q:ℂ)^2))^3
  have hD' : (z:ℂ)*(c:ℂ)+(γ 1 1:ℂ)≠0 := by simpa only [mul_comm (z:ℂ) (c:ℂ)] using hD
  field_simp [qn,cn,hD,hD']
end QEC.Coding.TannerLiftedProduct
