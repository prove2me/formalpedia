-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticCuspAffineBranch_taylor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:32:11.846207+00:00
-- url     : https://prove2.me/submissions/6cde35ea-82ed-40d1-a224-eaa24dc21ed9

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticCuspLocalizedTaylor_function
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticCuspLocalizedTaylor_invParameter
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedAffineCusp_taylor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJQCoefficient_analytic_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_comp_const_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_comp_pow


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (m : ℕ) (hm : 0<m) (r : ℚ) :
    lpsOriginalAnalyticCuspLocalizedTaylor (lpsOriginalAnalyticCuspAffineBranch m hm r)=
      (IsLocalization.Away.invSelf (S:=lpsOriginalComplexCuspLaurentRing)
        (PowerSeries.X : PowerSeries ℂ))^m *
        algebraMap (PowerSeries ℂ) lpsOriginalComplexCuspLaurentRing
          (PowerSeries.C ((Function.Periodic.qParam 1 (r:ℂ))⁻¹) *
            PowerSeries.expand m hm.ne' (PowerSeries.rescale (Function.Periodic.qParam 1 (r:ℂ))
              (lpsOriginalTaylorSeries lpsOriginalJQCoefficient))) := by
  rw [lpsOriginalAnalyticCuspAffineBranch,map_mul,map_pow,
    lpsOriginalAnalyticCuspLocalizedTaylor_invParameter,
    lpsOriginalAnalyticCuspLocalizedTaylor_function]
  change _ * algebraMap (PowerSeries ℂ) lpsOriginalComplexCuspLaurentRing
    (lpsOriginalTaylorSeries (lpsOriginalClearedAffineCusp m m r))=_
  have hf : AnalyticAt ℂ (fun q : ℂ=>lpsOriginalJQCoefficient
      (Function.Periodic.qParam 1 (r:ℂ)*q)) 0 :=
    lpsOriginalJQCoefficient_analytic_zero.fun_comp_of_eq
      (analyticAt_const.mul analyticAt_id) (mul_zero _)
  rw [lpsOriginalClearedAffineCusp_taylor m m hm.ne',Nat.sub_self,pow_zero,one_mul,
    lpsOriginalTaylorSeries_comp_pow hf m hm.ne',
    lpsOriginalTaylorSeries_comp_const_mul lpsOriginalJQCoefficient_analytic_zero]
end QEC.Coding.TannerLiftedProduct
