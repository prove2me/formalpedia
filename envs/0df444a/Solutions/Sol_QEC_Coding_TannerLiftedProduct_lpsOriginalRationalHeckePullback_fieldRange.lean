-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRationalHeckePullback_fieldRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:52:43.94119+00:00
-- url     : https://prove2.me/submissions/580ef342-ea1b-42db-8805-24446051edf2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [NeZero N] [NeZero p]
    (hN : 0 < N) (hp : 0 < p) (h4N : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ((lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN hp)).toSubfield.subtype.comp
      (lpsOriginalRationalHeckePullback N p hN hp h4N)).fieldRange =
        (lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield.map
          (lpsOriginalDilationFractionPullback p hp).toRingHom := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  ext y
  change (∃ x : lpsOriginalGeneratedFunctionFieldQ N hN,
    lpsOriginalDilationFractionPullback p hp (x : LPSOriginalHolomorphicFractionField) = y) ↔
      ∃ x ∈ (lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield,
        lpsOriginalDilationFractionPullback p hp x = y
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, x.property, hx⟩
  · rintro ⟨x, hx, he⟩
    exact ⟨⟨x, hx⟩, he⟩
end QEC.Coding.TannerLiftedProduct
