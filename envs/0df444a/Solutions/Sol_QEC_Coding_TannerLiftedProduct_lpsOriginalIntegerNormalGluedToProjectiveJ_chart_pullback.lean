-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedToProjectiveJ_chart_pullback
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:03:16.670485+00:00
-- url     : https://prove2.me/submissions/655cffbf-4d70-4296-8b10-d55e05390d43

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedChartMap_openImmersion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJChartMap_openImmersion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedToProjectiveJ_chart
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalChartProjection_comp
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedToProjectiveJ_preimage_chart
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) (hN : 0<N) (b : Bool) :
    IsPullback (lpsOriginalIntegerNormalGluedChartMap N hN b)
      (lpsOriginalIntegerNormalChartProjection N hN b)
      (lpsOriginalIntegerNormalGluedToProjectiveJ N hN)
      (lpsOriginalIntegerProjectiveJChartMap b) := by
  let := lpsOriginalIntegerNormalGluedChartMap_openImmersion N hN b
  let := lpsOriginalIntegerProjectiveJChartMap_openImmersion b
  have h : lpsOriginalIntegerNormalGluedChartMap N hN b ≫
      lpsOriginalIntegerNormalGluedToProjectiveJ N hN =
    lpsOriginalIntegerNormalChartProjection N hN b ≫
      lpsOriginalIntegerProjectiveJChartMap b :=
    (lpsOriginalIntegerNormalGluedToProjectiveJ_chart N hN b).trans
      (lpsOriginalIntegerNormalChartProjection_comp N hN b).symm
  refine { w := h, isLimit' := ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩ }
  · intro s
    apply IsOpenImmersion.lift (lpsOriginalIntegerNormalGluedChartMap N hN b) s.fst
    rw [← lpsOriginalIntegerNormalGluedToProjectiveJ_preimage_chart]
    rintro x ⟨x,rfl⟩
    refine ⟨s.snd x,?_⟩
    change (s.snd ≫ lpsOriginalIntegerProjectiveJChartMap b) x =
      (s.fst ≫ lpsOriginalIntegerNormalGluedToProjectiveJ N hN) x
    rw [s.condition]
  · intro s
    exact IsOpenImmersion.lift_fac _ _ _
  · intro s
    rw [← cancel_mono (lpsOriginalIntegerProjectiveJChartMap b),
      Category.assoc, ← h, IsOpenImmersion.lift_fac_assoc, s.condition]
  · intro s m h1 _
    simpa only [← cancel_mono (lpsOriginalIntegerNormalGluedChartMap N hN b),
      IsOpenImmersion.lift_fac] using h1
end QEC.Coding.TannerLiftedProduct
