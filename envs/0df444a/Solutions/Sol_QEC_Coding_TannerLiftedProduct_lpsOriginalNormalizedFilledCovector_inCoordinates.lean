-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedFilledCovector_inCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:33:47.536194+00:00
-- url     : https://prove2.me/submissions/038e3924-f39c-480f-9d01-a4e31ba60daa

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeCovectorCoordinates
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeCovectorNormalForm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizedCovectorCoefficient_cocycle
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold
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
open Filter Topology QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (sigma : LPSOriginalFilledCovectorRepresentatives N hN)
    (hmer : lpsOriginalFilledCovectorChartMeromorphic N hN sigma)
    (x y : LPSOriginalFilledCurve N)
    (hy : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      y ∈ (chartAt ℂ x).source) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ)) ℂ
      (Bundle.Trivial (LPSOriginalFilledCurve N) ℂ) x y x y
      (lpsOriginalNormalizedFilledCovector N hN sigma y) =
      ContinuousLinearMap.mul ℂ ℂ
        (toMeromorphicNFAt (lpsOriginalFilledCovectorChartCoefficient N hN sigma x)
          (chartAt ℂ x y) (chartAt ℂ x y)) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  have hz : chartAt ℂ x y ∈ ((chartAt ℂ x).symm.trans (chartAt ℂ y)).source := by
    change chartAt ℂ x y ∈ (chartAt ℂ x).target ∧
      (chartAt ℂ x).symm (chartAt ℂ x y) ∈ (chartAt ℂ y).source
    exact ⟨(chartAt ℂ x).map_source hy,
      by rw [(chartAt ℂ x).left_inv hy]; exact mem_chart_source ℂ y⟩
  have hk := lpsOriginalNormalizedCovectorCoefficient_cocycle N hN sigma hmer x y
    (chartAt ℂ x y) hz
  have he : ((chartAt ℂ x).symm.trans (chartAt ℂ y)) (chartAt ℂ x y) =
      chartAt ℂ y y := by
    rw [OpenPartialHomeomorph.trans_apply, (chartAt ℂ x).left_inv hy]
  dsimp only at hk
  rw [he] at hk
  have ht : (trivializationAt ℂ (Bundle.Trivial (LPSOriginalFilledCurve N) ℂ) x).continuousLinearMapAt ℂ y = ContinuousLinearMap.id ℂ ℂ :=
    Bundle.Trivial.continuousLinearMapAt_trivialization ℂ _ ℂ y
  rw [ContinuousLinearMap.inCoordinates, ht, ContinuousLinearMap.id_comp,
    TangentBundle.symmL_trivializationAt_eq_core hy, tangentBundleCore_coordChange_achart]
  have heq : extChartAt 𝓘(ℂ) y ∘ (extChartAt 𝓘(ℂ) x).symm =
      (((chartAt ℂ x).symm.trans (chartAt ℂ y)) : ℂ → ℂ) := rfl
  rw [heq]
  simp only [modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ]
  change (ContinuousLinearMap.mul ℂ ℂ
    (toMeromorphicNFAt (lpsOriginalFilledCovectorChartCoefficient N hN sigma y)
      (chartAt ℂ y y) (chartAt ℂ y y))).comp
        (fderiv ℂ (((chartAt ℂ x).symm.trans (chartAt ℂ y)) : ℂ → ℂ)
          (chartAt ℂ x y)) = _
  apply ContinuousLinearMap.ext
  intro v
  change toMeromorphicNFAt (lpsOriginalFilledCovectorChartCoefficient N hN sigma y)
    (chartAt ℂ y y) (chartAt ℂ y y) *
      (fderiv ℂ (((chartAt ℂ x).symm.trans (chartAt ℂ y)) : ℂ → ℂ)
        (chartAt ℂ x y)) v =
      toMeromorphicNFAt (lpsOriginalFilledCovectorChartCoefficient N hN sigma x)
        (chartAt ℂ x y) (chartAt ℂ x y) * v
  rw [fderiv_eq_deriv_mul, ← mul_assoc, ← hk]
end QEC.Coding.TannerLiftedProduct
