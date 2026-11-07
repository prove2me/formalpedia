-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Dilate_cusp_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:10:59.979474+00:00
-- url     : https://prove2.me/submissions/d297d4cf-6bf1-47c9-aa41-43a67c87ddac

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2Affine_cusp_tendsto
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Dilate_eq
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
theorem _root_.solution (q m : ℕ) [Fact q.Prime] (hm : 0<m)
    (γ : SL(2,ℤ)) :
    Tendsto (lpsQuadraticE2Dilate q m hm ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 ((gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ *
        ∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q)*
          (((Int.gcd ((q:ℤ)*(m:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0)
            ((q:ℤ)*γ 1 0):ℕ):ℂ)^2/((q:ℂ)^2*(m:ℂ)^2)))) := by
  classical
  have hs := tendsto_finsetSum Finset.univ (fun (r : Fin q) hr =>
    (lpsE2Affine_cusp_tendsto m q hm (Fact.out : q.Prime).pos (r.val:ℤ) γ).const_mul
      (lpsQuadraticE2Character q (r.val:ZMod q)))
  have h := hs.const_mul (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹
  have he : (lpsQuadraticE2Dilate q m hm ∣[(2:ℤ)] γ) = (fun z : ℍ =>
      (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ *
        ∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q)*
          (((fun w : ℍ => EisensteinSeries.E2
            (lpsE2AffineMatrix m hm ((r.val:ℝ)/(q:ℝ)) • w)) ∣[(2:ℤ)] γ) z)) := by
    rw [lpsQuadraticE2Dilate_eq]
    funext z
    simp only [ModularForm.SL_slash_apply]
    rw [mul_assoc,Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [he]
  simpa only [Int.cast_natCast] using h
end QEC.Coding.TannerLiftedProduct
