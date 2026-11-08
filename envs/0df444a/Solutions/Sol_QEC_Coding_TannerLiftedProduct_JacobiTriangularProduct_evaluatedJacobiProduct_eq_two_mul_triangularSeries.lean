-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.evaluatedJacobiProduct_eq_two_mul_triangularSeries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:56:52.951237+00:00
-- url     : https://prove2.me/submissions/50b19ee6-7b0d-4e7f-8c3b-8c5c49528de1

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeProduct
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.Topology.WithTopology
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTriangularProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTriangularProduct_summable_triangularProductTerm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTriangularProduct_hasSum_triangularProductTerm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTriangularProduct_hasSum_triangularDiagonal_nonnegative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTriangularProduct_hasSum_triangularDiagonal_negative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_signedEuler_jtpPositiveTerm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammer_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_succ_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_right
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_succ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qPochhammer_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiSignedCubeSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiSignedCubeSeriesRaw
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiWeightedSquareSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiWeightedTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalBilateralTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalTriangularThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiEulerSixProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiEulerSquareProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiTriangularProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalBilateralTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalTriangularThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_integerTriangularRoots_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiParityReindex_inl
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiParityReindex_inr
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedEuler_jtpPositiveTerm
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammer_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_succ_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_right
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_succ
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qPochhammer_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiSignedCubeSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiSignedCubeSeriesRaw
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiWeightedSquareSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiWeightedTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalBilateralTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalIntegerThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalTriangularThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiEulerSixProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiEulerSquareProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiThetaProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiTriangularProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalBilateralTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalIntegerThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalTriangularThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.integerTriangularRoots_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiParityReindex_inl
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiParityReindex_inr
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


section
namespace QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace JacobiTriangularProduct
open JacobiGeneralCore.FormalPowerSeries
attribute [local instance] discreteRatUniformSpace
attribute [local instance] discreteRatTopologicalSpace
attribute [local instance] discreteRatUniformity
attribute [local instance] discreteRatTopology
attribute [local instance] discreteTargetUniformSpace
attribute [local instance] discreteTargetTopologicalSpace
attribute [local instance] discreteTargetUniformity
attribute [local instance] discreteTargetTopology
private theorem hasSum_split_diagonal (f : ℕ × ℕ → Target)
    {a b : Target}
    (h1 : HasSum (fun p : ℕ × ℕ => f (p.2 + p.1, p.2)) a)
    (h2 : HasSum (fun p : ℕ × ℕ => f (p.2, p.2 + p.1 + 1)) b) :
    HasSum f (a + b) :=
  diagonalEquiv.symm.hasSum_iff.mp (h1.sum h2)
private theorem hasSum_of_hasSum_fiberwise {f : ℕ × ℕ → Target}
    {g : ℕ → Target} (hf : Summable f)
    (hrow : ∀ k : ℕ, HasSum (fun m : ℕ => f (k, m)) (g k)) :
    HasSum f (∑' k : ℕ, g k) := by
  rw [(hf.hasSum.prod_fiberwise hrow).tsum_eq]
  exact hf.hasSum
private theorem summable_triangularDiagonal_nonnegative :
    Summable (fun p : ℕ × ℕ =>
      triangularProductTerm (p.2 + p.1, p.2)) := by
  apply summable_triangularProductTerm.comp_injective
  rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ h
  simp only at h
  injection h with hsum h₂
  congr
  omega
private theorem summable_triangularDiagonal_negative :
    Summable (fun p : ℕ × ℕ =>
      triangularProductTerm (p.2, p.2 + p.1 + 1)) := by
  apply summable_triangularProductTerm.comp_injective
  rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ h
  simp only at h
  injection h with h₂ hsum
  congr
  omega
private theorem hasSum_triangularDiagonal_nonnegative_part :
    HasSum (fun p : ℕ × ℕ =>
      triangularProductTerm (p.2 + p.1, p.2))
      evaluatedTriangularSeries := by
  exact hasSum_of_hasSum_fiberwise
    summable_triangularDiagonal_nonnegative
    hasSum_triangularDiagonal_nonnegative
private theorem hasSum_triangularDiagonal_negative_part :
    HasSum (fun p : ℕ × ℕ =>
      triangularProductTerm (p.2, p.2 + p.1 + 1))
      evaluatedTriangularSeries := by
  exact hasSum_of_hasSum_fiberwise
    summable_triangularDiagonal_negative
    hasSum_triangularDiagonal_negative
end JacobiTriangularProduct
end QEC.Coding.TannerLiftedProduct
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
open QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct
open JacobiGeneralCore.FormalPowerSeries
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.discreteRatUniformSpace
attribute [local instance] discreteRatUniformSpace
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.discreteRatTopologicalSpace
attribute [local instance] discreteRatTopologicalSpace
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.discreteRatUniformity
attribute [local instance] discreteRatUniformity
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.discreteRatTopology
attribute [local instance] discreteRatTopology
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.discreteTargetUniformSpace
attribute [local instance] discreteTargetUniformSpace
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.discreteTargetTopologicalSpace
attribute [local instance] discreteTargetTopologicalSpace
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.discreteTargetUniformity
attribute [local instance] discreteTargetUniformity
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.discreteTargetTopology
attribute [local instance] discreteTargetTopology
namespace QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct
theorem _root_.solution :
    (evaluatedPochhammerInf * evalOuter (qPochhammerInf (-sourceQ))) *
        evalOuter (qPochhammerInf (-sourceOne)) =
      2 * evaluatedTriangularSeries := by
  have hdiagonal : HasSum triangularProductTerm
      (evaluatedTriangularSeries + evaluatedTriangularSeries) :=
    hasSum_split_diagonal triangularProductTerm
      hasSum_triangularDiagonal_nonnegative_part
      hasSum_triangularDiagonal_negative_part
  rw [hasSum_triangularProductTerm.unique hdiagonal]
  ring
end QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct
