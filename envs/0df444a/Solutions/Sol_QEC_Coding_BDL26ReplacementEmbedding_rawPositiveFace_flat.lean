-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rawPositiveFace_flat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:20:23.844215+00:00
-- url     : https://prove2.me/submissions/8434b1ff-db79-4f74-8267-e68c0704debf

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rawPositiveFace_slot
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (f : P.Face) (c : RawPositiveCell S) :
    rxFaceFlatEquiv P S (rawPositiveFace P S f c) = (f, .inl (rawPositiveCellEquiv S c)) := by
  change (Equiv.prodCongr (Equiv.refl _)
    ((patchSlotRawFlatEquiv S).trans (rawFlatCellEquiv S)))
      (rxFaceSlotEquiv P S (rawPositiveFace P S f c)) = _
  rw [rawPositiveFace_slot]
  change (f, rawFlatCellEquiv S ((patchSlotRawFlatEquiv S)
    ((patchSlotRawFlatEquiv S).symm (.inl c)))) = _
  rw [Equiv.apply_symm_apply]
  rfl
end QEC.Coding.BDL26ReplacementEmbedding
