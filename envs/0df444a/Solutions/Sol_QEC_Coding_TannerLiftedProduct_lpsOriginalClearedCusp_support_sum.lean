-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalClearedCusp_support_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:19:38.875193+00:00
-- url     : https://prove2.me/submissions/0f0c4308-ae45-4c0e-a067-9c8636642dc2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (M B : ℕ) (P : Polynomial (Polynomial ℂ)) :
    lpsOriginalClearedCusp M B P =
      ∑ s : LPSOriginalBivariateSupport P, fun q =>
        (P.coeff s.1.val).coeff s.2.val *
          lpsOriginalClearedMonomial M B s.2.val s.1.val q := by
  classical
  unfold lpsOriginalClearedCusp
  rw [Fintype.sum_sigma]
  change _ = ∑ k : P.support, ∑ i : (P.coeff k.val).support,
    fun q => (P.coeff k.val).coeff i.val * lpsOriginalClearedMonomial M B i.val k.val q
  have inner (k : P.support) :
      (∑ i : (P.coeff k.val).support, fun q =>
        (P.coeff k.val).coeff i.val * lpsOriginalClearedMonomial M B i.val k.val q) =
      ∑ i ∈ (P.coeff k.val).support, fun q =>
        (P.coeff k.val).coeff i * lpsOriginalClearedMonomial M B i k.val q :=
    Finset.sum_coe_sort (P.coeff k.val).support
      (fun i : ℕ => fun q : ℂ =>
        (P.coeff k.val).coeff i * lpsOriginalClearedMonomial M B i k.val q)
  simp_rw [inner]
  exact (Finset.sum_coe_sort P.support
    (fun k => ∑ i ∈ (P.coeff k).support, fun q =>
      (P.coeff k).coeff i * lpsOriginalClearedMonomial M B i k q)).symm
end QEC.Coding.TannerLiftedProduct
