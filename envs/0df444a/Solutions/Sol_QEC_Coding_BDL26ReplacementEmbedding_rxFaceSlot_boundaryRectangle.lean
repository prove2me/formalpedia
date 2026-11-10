-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rxFaceSlot_boundaryRectangle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:35:06.771373+00:00
-- url     : https://prove2.me/submissions/b1b357e0-82a3-49fd-a843-33464ba39d8c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (f : P.Face) (side copy : BDL26FiniteTannerSquare.Two) (i : Fin S.half)
    (endpoint : BDL26FiniteTannerSquare.Two) :
    rxFaceSlotEquiv P S (boundaryRectangleFace P S f side copy i endpoint) =
      (f, .inl (.inr (side, i, copy, endpoint))) := by
  have h : (faceCornerBoundaryEquiv P).symm (faceCornerBoundaryEdge P (f, side)) =
      (f, side) := (faceCornerBoundaryEquiv P).symm_apply_apply (f, side)
  change ((((faceCornerBoundaryEquiv P).symm (faceCornerBoundaryEdge P (f, side))).1,
    .inl (.inr (((faceCornerBoundaryEquiv P).symm
      (faceCornerBoundaryEdge P (f, side))).2, i, copy, endpoint))) : P.Face × PatchSlot S) = _
  rw [h]
end QEC.Coding.BDL26ReplacementEmbedding
