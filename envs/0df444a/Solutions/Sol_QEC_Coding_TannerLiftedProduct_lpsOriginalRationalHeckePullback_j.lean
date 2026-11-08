-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRationalHeckePullback_j
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:12:35.788191+00:00
-- url     : https://prove2.me/submissions/954593c1-a3e5-471b-af94-a9a7615aa547

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
      ⟨lpsOriginalJInFractionField, lpsOriginalJInFractionField_mem_generatedQ N hN⟩ :
        lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN hp)) :
          LPSOriginalHolomorphicFractionField) = lpsOriginalJNInFractionField p hp := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [lpsOriginalRationalHeckePullback_coe]
  exact lpsOriginalDilationFractionPullback_j p hp
end QEC.Coding.TannerLiftedProduct
