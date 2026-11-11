-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.actualFlatImage_subset_charge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:18:46.40368+00:00
-- url     : https://prove2.me/submissions/809a0c0c-d74a-428e-85d7-d9e59189bb95

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_actualSlotImage_subset_charge
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_chargePatchSlot_flat
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (cell : FlatCell S) :
    actualFlatImage P S J (f, cell) ⊆ actualFlatImage P S J (f, .inl (charge S cell)) := by
  let e := (patchSlotRawFlatEquiv S).trans (rawFlatCellEquiv S)
  let slot := e.symm cell
  have hs : e slot = cell := e.apply_symm_apply cell
  have hc : e (chargePatchSlot S slot) = .inl (charge S cell) := by
    change rawFlatCellEquiv S (patchSlotToRawFlat S (chargePatchSlot S slot)) = _
    rw [chargePatchSlot_flat]
    exact congrArg (fun c => Sum.inl (charge S c)) hs
  have h := actualSlotImage_subset_charge P S J f slot
  change rxFaceImage P S J ((rxFaceSlotEquiv P S).symm (f, e.symm cell)) ⊆
    rxFaceImage P S J ((rxFaceSlotEquiv P S).symm (f, e.symm (.inl (charge S cell))))
  rw [← hc, e.symm_apply_apply]
  exact h
end QEC.Coding.BDL26ReplacementEmbedding
