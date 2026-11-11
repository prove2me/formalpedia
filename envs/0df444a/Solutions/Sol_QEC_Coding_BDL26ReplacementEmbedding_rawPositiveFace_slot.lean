-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rawPositiveFace_slot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:14:48.127848+00:00
-- url     : https://prove2.me/submissions/8551faaf-ebdc-41e0-acd9-30ba1a3bfbe1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rxFaceSlot_planar
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rxFaceSlot_oldZ
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rxFaceSlot_pathStrip

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
    rxFaceSlotEquiv P S (rawPositiveFace P S f c) =
      (f, rawFlatToPatchSlot S (.inl c)) := by
  rcases c with ⟨copy, (⟨i, a⟩ | last), (⟨j, b⟩ | last')⟩
  · exact rxFaceSlot_planar P S f i j copy a b
  · exact rxFaceSlot_pathStrip P S f 1 copy i a
  · exact rxFaceSlot_pathStrip P S f 0 copy j b
  · exact rxFaceSlot_oldZ P S f copy
end QEC.Coding.BDL26ReplacementEmbedding
