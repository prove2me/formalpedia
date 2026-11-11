-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rx_constructed_degrees
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:31:59.008904+00:00
-- url     : https://prove2.me/submissions/c1baaaa4-62f6-4edc-b3b6-41123b19aa9f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_qzIncidentFace_card_le_four
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_rx_boundedValence
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_xqIncidentFace_card_le_four
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rx_boundedValence


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
open BDL26BoundedValence
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (h : BoundedValence P) :
    BoundedValence (rxReplacementPresentation P S) ∧
      (∀ e : XQEdge (rxReplacementPresentation P S),
        Fintype.card (XQIncidentFace (rxReplacementPresentation P S) e) ≤ 4) ∧
      (∀ e : QZEdge (rxReplacementPresentation P S),
        Fintype.card (QZIncidentFace (rxReplacementPresentation P S) e) ≤ 4) := by
  have hv := BDL26BoundedValence.rx_boundedValence P A4 R S h
  exact ⟨hv, xqIncidentFace_card_le_four _ hv, qzIncidentFace_card_le_four _ hv⟩
end QEC.Coding.BDL26ReplacementEmbedding
