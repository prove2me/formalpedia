-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsE2Difference_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:28:26.759194+00:00
-- url     : https://prove2.me/submissions/7f20d8ec-2737-46fe-9060-6262a899214d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2Dilated_hasSum
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
theorem _root_.solution (m : ℕ) (hm : 0 < m) (z : ℍ) :
    HasSum (fun n : ℕ => lpsE2DifferenceCoefficient m n*Function.Periodic.qParam 1 (z:ℂ)^n)
      (lpsE2Difference m hm z) := by
  have hE : HasSum (fun n : ℕ => (if n=0 then 1 else -24*(ArithmeticFunction.sigma 1 n:ℂ))*
      Function.Periodic.qParam 1 (z:ℂ)^n) (EisensteinSeries.E2 z) := by
    simpa only [smul_eq_mul,Function.Periodic.qParam,Complex.ofReal_one,div_one] using
      EisensteinSeries.hasSum_qExpansion_E2 (z:=z)
  have hM := (lpsE2Dilated_hasSum m hm z).mul_left (m:ℂ)
  have h := hE.sub hM
  change HasSum _ (lpsE2Difference m hm z) at h
  apply h.congr_fun
  intro n
  simp only [lpsE2DifferenceCoefficient]
  ring
end QEC.Coding.TannerLiftedProduct
