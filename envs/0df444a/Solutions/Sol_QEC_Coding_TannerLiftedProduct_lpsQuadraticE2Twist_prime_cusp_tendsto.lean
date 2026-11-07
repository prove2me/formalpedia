-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_prime_cusp_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:08:24.888484+00:00
-- url     : https://prove2.me/submissions/fdbfde2f-553c-4895-80ab-7d0fc6bdcd48

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2ShiftAtPrimeCusp_tendsto
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2PrimeCusp_sum
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
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    Tendsto (lpsQuadraticE2Twist q ∣[(2:ℤ)] lpsE2PrimeCuspMatrix q)
      UpperHalfPlane.atImInfty (𝓝 (lpsQuadraticE2Character q (-1:ZMod q)*((q:ℂ)^2-1)/
        gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))) := by
  classical
  have hs := tendsto_finsetSum Finset.univ (fun (r : Fin q) hr =>
    (lpsE2ShiftAtPrimeCusp_tendsto q r).const_mul
      (lpsQuadraticE2Character q (r.val:ZMod q)))
  rw [lpsQuadraticE2PrimeCusp_sum q hq2] at hs
  have h := hs.const_mul (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹
  have he : (lpsQuadraticE2Twist q ∣[(2:ℤ)] lpsE2PrimeCuspMatrix q) = (fun z : ℍ =>
      (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ *
        ∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q)*
          (((fun w : ℍ => EisensteinSeries.E2 (((r.val:ℝ)/(q:ℝ)) +ᵥ w))
            ∣[(2:ℤ)] lpsE2PrimeCuspMatrix q) z)) := by
    funext z
    simp only [ModularForm.SL_slash_apply,lpsQuadraticE2Twist]
    rw [mul_assoc,Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [he]
  have hl : (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ *
      (lpsQuadraticE2Character q (-1:ZMod q)*((q:ℂ)^2-1)) =
      lpsQuadraticE2Character q (-1:ZMod q)*((q:ℂ)^2-1)/
        gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)) := by
    rw [div_eq_mul_inv];ring
  rw [hl] at h
  exact h
end QEC.Coding.TannerLiftedProduct
