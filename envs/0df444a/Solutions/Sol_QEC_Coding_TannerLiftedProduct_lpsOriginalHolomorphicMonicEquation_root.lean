-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicMonicEquation_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:50:28.116346+00:00
-- url     : https://prove2.me/submissions/f66d6407-d31f-4bea-bc54-2b15f267821d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.Algebra.Polynomial.BigOperators
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicDeltaPowerAtLevel_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicRatioEquation_root


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (k : ℕ)
    (A : LPSOriginalMeromorphicLevelForm N k) (f : ℍ → ℂ)
    (hf : ∀ τ, A τ = ModularForm.discriminant τ^k * f τ) (τ : ℍ) :
    (lpsOriginalHolomorphicMonicEquation N k A).eval₂
      (Polynomial.evalRingHom (lpsOriginalJInvariant τ)) (f τ) = 0 := by
  rw [lpsOriginalHolomorphicMonicEquation,Polynomial.eval₂_mul]
  have h := lpsOriginalMeromorphicRatioEquation_root N k A
    (lpsOriginalMeromorphicDeltaPowerAtLevel N k) f
    (fun τ => by rw [lpsOriginalMeromorphicDeltaPowerAtLevel_apply];exact hf τ) τ
  rw [h,mul_zero]
end QEC.Coding.TannerLiftedProduct
