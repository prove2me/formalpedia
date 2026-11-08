-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRationalHeckePullback_jN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:13:02.032253+00:00
-- url     : https://prove2.me/submissions/a885150b-c97c-4c5a-a4dc-57cc11f54d49

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalHeckePullback_coe

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [NeZero N] [NeZero p]
    (hN : 0 < N) (hp : 0 < p) (h4N : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ((lpsOriginalRationalHeckePullback N p hN hp h4N
      ⟨lpsOriginalJNInFractionField N hN,
        IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)⟩ :
        lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN hp)) :
          LPSOriginalHolomorphicFractionField) =
            lpsOriginalJNInFractionField (N*p) (Nat.mul_pos hN hp) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [lpsOriginalRationalHeckePullback_coe]
  exact lpsOriginalDilationFractionPullback_jN N p hN hp
end QEC.Coding.TannerLiftedProduct
