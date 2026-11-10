-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rxFaceSlot_terminalRung
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:35:03.872324+00:00
-- url     : https://prove2.me/submissions/5fe40829-de99-4133-a319-a1f849f58702

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
    (side copy : BDL26FiniteTannerSquare.Two) :
    rxFaceSlotEquiv P S (terminalRungFace P S f side copy) =
      (f, .inr (.inl (side, .inr 0, copy))) := by
  let e := Equiv.ofBijective (faceCornerWedge P) (faceCornerWedge_bijective P)
  have h : e.symm (faceCornerWedge P (f, side)) = (f, side) := e.symm_apply_apply (f, side)
  change (((e.symm (faceCornerWedge P (f, side))).1,
    .inr (.inl ((e.symm (faceCornerWedge P (f, side))).2, .inr 0, copy))) : P.Face × PatchSlot S) = _
  rw [h]
end QEC.Coding.BDL26ReplacementEmbedding
