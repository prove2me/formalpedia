-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rxFaceSlot_pathStrip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:35:22.743292+00:00
-- url     : https://prove2.me/submissions/4f85f77a-c68b-40c7-8329-6f7319899195

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_faceCornerWedge_bijective
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale) (f : P.Face)
    (side copy : BDL26FiniteTannerSquare.Two) (i : Fin S.half)
    (endpoint : BDL26FiniteTannerSquare.Two) :
    rxFaceSlotEquiv P S (pathStripFace P S f side copy i endpoint) =
      (f, .inr (.inl (side, .inl (copy, i), endpoint))) := by
  let e := Equiv.ofBijective (faceCornerWedge P) (faceCornerWedge_bijective P)
  have h : e.symm (faceCornerWedge P (f, side)) = (f, side) := e.symm_apply_apply (f, side)
  change (((e.symm (faceCornerWedge P (f, side))).1,
    .inr (.inl ((e.symm (faceCornerWedge P (f, side))).2, .inl (copy, i), endpoint))) : P.Face × PatchSlot S) = _
  rw [h]
end QEC.Coding.BDL26ReplacementEmbedding
