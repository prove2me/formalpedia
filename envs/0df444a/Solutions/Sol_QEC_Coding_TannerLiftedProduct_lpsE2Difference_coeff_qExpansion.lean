-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsE2Difference_coeff_qExpansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:30:03.22994+00:00
-- url     : https://prove2.me/submissions/a6a9a7eb-9670-4dff-b284-ebbfb93475a9

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2Difference_add_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2Difference_hasSum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFunction_periodic_comp_ofComplex
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
theorem _root_.solution (m : ℕ) (hm : 0 < m) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsE2Difference m hm))=
      lpsE2DifferenceCoefficient m n := by
  have hp := lpsFunction_periodic_comp_ofComplex _ (lpsE2Difference_add_one m hm)
  have hh := lpsE2Difference_mdifferentiable m hm
  have hb : UpperHalfPlane.IsBoundedAtImInfty (lpsE2Difference m hm) := by
    have ht := lpsE2Difference_cusp_tendsto m hm (1:SL(2,ℤ))
    simp only [SlashAction.slash_one] at ht
    exact ht.isBigO_one ℝ
  have ha := UpperHalfPlane.analyticAt_cuspFunction_zero (by norm_num : (0:ℝ)<1) hp hh hb
  let f : C(ℍ,ℂ) := ⟨lpsE2Difference m hm,hh.continuous⟩
  symm
  exact UpperHalfPlane.qExpansion_coeff_unique f (by norm_num : (0:ℝ)<1) ha
    (fun z => by simpa only [smul_eq_mul,f,ContinuousMap.coe_mk] using
      lpsE2Difference_hasSum m hm z) n
end QEC.Coding.TannerLiftedProduct
