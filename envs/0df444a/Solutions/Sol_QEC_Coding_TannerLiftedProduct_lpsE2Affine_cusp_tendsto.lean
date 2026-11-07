-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsE2Affine_cusp_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:09:16.274203+00:00
-- url     : https://prove2.me/submissions/a7be942c-c176-44b7-b9ec-12d9d9040fb8

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2_slash_tendsto_integer_column
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2IntegerColumn_gcd_pos
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_det
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_coe
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_slash
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
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (m q : ℕ) (hm : 0<m) (hq : 0<q)
    (r : ℤ) (γ : SL(2,ℤ)) :
    Tendsto ((fun z : ℍ => EisensteinSeries.E2
        (lpsE2AffineMatrix m hm ((r:ℝ)/(q:ℝ)) • z)) ∣[(2:ℤ)] γ)
      UpperHalfPlane.atImInfty
      (𝓝 (((Int.gcd ((q:ℤ)*(m:ℤ)*γ 0 0+r*γ 1 0) ((q:ℤ)*γ 1 0):ℕ):ℂ)^2/
        ((q:ℂ)^2*(m:ℂ)^2))) := by
  let M : GL (Fin 2) ℝ := lpsE2AffineMatrix m hm ((r:ℝ)/(q:ℝ)) *
    Matrix.SpecialLinearGroup.mapGL ℝ γ
  have hdet : M.det.val=(m:ℝ) := by
    calc M.det.val=(lpsE2AffineMatrix m hm ((r:ℝ)/(q:ℝ))).det.val := by simp [M]
         _=(m:ℝ) := lpsE2AffineMatrix_det m hm _
  have hp : 0<M.det.val := by rw [hdet];exact_mod_cast hm
  have hqR : (q:ℝ)≠0 := by exact_mod_cast hq.ne'
  have ha : M 0 0=(((q:ℤ)*(m:ℤ)*γ 0 0+r*γ 1 0:ℤ):ℝ)/(q:ℝ) := by
    change ((lpsE2AffineMatrix m hm ((r:ℝ)/(q:ℝ)):Matrix (Fin 2) (Fin 2) ℝ)*
      ((γ:Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ))) 0 0=_
    rw [lpsE2AffineMatrix_coe]
    simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.map,Matrix.of_apply]
    field_simp
  have hc : M 1 0=(((q:ℤ)*γ 1 0:ℤ):ℝ)/(q:ℝ) := by
    change ((lpsE2AffineMatrix m hm ((r:ℝ)/(q:ℝ)):Matrix (Fin 2) (Fin 2) ℝ)*
      ((γ:Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ))) 1 0=_
    rw [lpsE2AffineMatrix_coe]
    simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.map,Matrix.of_apply,hqR]
  have hg := lpsE2IntegerColumn_gcd_pos M hp _ _ (q:ℝ) ha hc
  have hl := lpsE2_slash_tendsto_integer_column M hp _ _ (q:ℝ) hqR ha hc hg
  let G : ℕ := Int.gcd ((q:ℤ)*(m:ℤ)*γ 0 0+r*γ 1 0) ((q:ℤ)*γ 1 0)
  have he : (EisensteinSeries.E2 ∣[(2:ℤ)] M) =
      (fun z : ℍ => (m:ℂ)*(((fun w : ℍ => EisensteinSeries.E2
        (lpsE2AffineMatrix m hm ((r:ℝ)/(q:ℝ)) • w)) ∣[(2:ℤ)] γ) z)) := by
    rw [show M=lpsE2AffineMatrix m hm ((r:ℝ)/(q:ℝ))*Matrix.SpecialLinearGroup.mapGL ℝ γ from rfl,
      SlashAction.slash_mul,lpsE2AffineMatrix_slash]
    change ((fun z : ℍ => (m:ℂ)*EisensteinSeries.E2
      (lpsE2AffineMatrix m hm ((r:ℝ)/(q:ℝ)) • z)) ∣[(2:ℤ)] γ)=_
    funext z
    simp only [ModularForm.SL_slash_apply]
    ring
  have hmC : (m:ℂ)≠0 := by exact_mod_cast hm.ne'
  have hqC : (q:ℂ)≠0 := by exact_mod_cast hq.ne'
  have h := hl.const_mul (m:ℂ)⁻¹
  have hfn : (fun z : ℍ => (m:ℂ)⁻¹*(EisensteinSeries.E2 ∣[(2:ℤ)] M) z) =
      ((fun w : ℍ => EisensteinSeries.E2
        (lpsE2AffineMatrix m hm ((r:ℝ)/(q:ℝ)) • w)) ∣[(2:ℤ)] γ) := by
    rw [he]
    funext z
    simp [hmC]
  have hval : (m:ℂ)⁻¹*((G:ℂ)/(q:ℂ))^2/(M.det.val:ℂ) =
      (G:ℂ)^2/((q:ℂ)^2*(m:ℂ)^2) := by
    rw [hdet]
    simp only [Complex.ofReal_natCast]
    field_simp [hmC,hqC]
  simp only [hfn,Complex.ofReal_natCast,← mul_div_assoc] at h
  change Tendsto _ UpperHalfPlane.atImInfty
    (𝓝 ((m:ℂ)⁻¹*((G:ℂ)/(q:ℂ))^2/(M.det.val:ℂ))) at h
  rw [hval] at h
  exact h
end QEC.Coding.TannerLiftedProduct
