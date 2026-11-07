-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsE2_slash_tendsto_of_column
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:06:14.409608+00:00
-- url     : https://prove2.me/submissions/b7343bc0-f80b-4690-8286-ca0e0e6d6949

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2SLInverse_real_matrix
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2_slash_factor_tendsto
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (M : GL (Fin 2) ℝ)
    (hd : 0<M.det.val) (δ : SL(2,ℤ)) (g : ℝ) (hg : g≠0)
    (ha : (δ 0 0:ℝ)*g=M 0 0) (hc : (δ 1 0:ℝ)*g=M 1 0) :
    Tendsto (EisensteinSeries.E2 ∣[(2:ℤ)] M) UpperHalfPlane.atImInfty
      (𝓝 ((g:ℂ)^2/(M.det.val:ℂ))) := by
  let h : GL (Fin 2) ℝ := (Matrix.SpecialLinearGroup.mapGL ℝ δ)⁻¹*M
  have hdδ : (δ 0 0:ℝ)*(δ 1 1:ℝ)-(δ 0 1:ℝ)*(δ 1 0:ℝ)=1 := by
    have hdet : δ 0 0*δ 1 1-δ 0 1*δ 1 0=1 := by
      simpa only [Matrix.det_fin_two] using δ.det_coe
    exact_mod_cast hdet
  have hh10 : h 1 0=0 := by
    change ((((Matrix.SpecialLinearGroup.mapGL ℝ δ)⁻¹:GL (Fin 2) ℝ):Matrix (Fin 2) (Fin 2) ℝ)*
      (M:Matrix (Fin 2) (Fin 2) ℝ)) 1 0=0
    rw [lpsE2SLInverse_real_matrix]
    simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply]
    rw [← ha,← hc]
    ring
  have hh00 : h 0 0=g := by
    change ((((Matrix.SpecialLinearGroup.mapGL ℝ δ)⁻¹:GL (Fin 2) ℝ):Matrix (Fin 2) (Fin 2) ℝ)*
      (M:Matrix (Fin 2) (Fin 2) ℝ)) 0 0=g
    rw [lpsE2SLInverse_real_matrix]
    simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply]
    rw [← ha,← hc]
    linear_combination g*hdδ
  have hhdet : h.det.val=M.det.val := by simp [h]
  have hh11 : h 1 1=M.det.val/g := by
    have he : g*h 1 1=M.det.val := by
      have he := hhdet
      change Matrix.det (h:Matrix (Fin 2) (Fin 2) ℝ)=M.det.val at he
      simpa only [Matrix.det_fin_two,hh00,hh10,mul_zero,sub_zero] using he
    apply (eq_div_iff hg).2
    simpa [mul_comm] using he
  have hm : M=Matrix.SpecialLinearGroup.mapGL ℝ δ*h := by simp [h]
  have hp : 0<h.det.val := by rw [hhdet];exact hd
  have hl := lpsE2_slash_factor_tendsto δ h hh10 hp
  have hdc : (M.det.val:ℂ)≠0 := by exact_mod_cast hd.ne'
  have hgc : (g:ℂ)≠0 := by exact_mod_cast hg
  have he : (h.det.val:ℂ)*(h 1 1:ℂ)^(-(2:ℤ))=(g:ℂ)^2/(M.det.val:ℂ) := by
    rw [hhdet,hh11]
    simp only [Complex.ofReal_div,zpow_neg,zpow_ofNat]
    field_simp [hdc,hgc]
  rw [he] at hl
  simpa only [← hm] using hl
end QEC.Coding.TannerLiftedProduct
