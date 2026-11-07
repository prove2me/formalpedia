-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicRatioNormCoefficient_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:38:39.622784+00:00
-- url     : https://prove2.me/submissions/da3a5f0f-3d23-4847-bf21-9afc2e49cab4

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLevelOne_unique_polynomial_j


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k) (c : ℂ) :
    (lpsOriginalMeromorphicRatioNormCoefficient N k A B c).natDegree ≤
      k * Nat.card (LPSOriginalMeromorphicCosets N) ∧ ∀ τ : ℍ,
    lpsOriginalMeromorphicRatioNorm N k A B c τ =
      ModularForm.discriminant τ ^ (k * Nat.card (LPSOriginalMeromorphicCosets N)) *
        (lpsOriginalMeromorphicRatioNormCoefficient N k A B c).eval (lpsOriginalJInvariant τ) :=
  Classical.choose_spec
    (lpsOriginalLevelOne_unique_polynomial_j (k*Nat.card (LPSOriginalMeromorphicCosets N))
      (lpsOriginalMeromorphicRatioNorm N k A B c)).exists
end QEC.Coding.TannerLiftedProduct
