-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rz_constructed_degrees
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:32:02.201237+00:00
-- url     : https://prove2.me/submissions/4ece41be-b678-4035-943a-fac035ad9c59

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
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_rz_boundedValence
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_xqIncidentFace_card_le_four


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
open BDL26BoundedValence
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (h : BoundedValence P) :
    let P' := BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S
    BoundedValence P' ∧
      (∀ e : XQEdge P', Fintype.card (XQIncidentFace P' e) ≤ 4) ∧
      (∀ e : QZEdge P', Fintype.card (QZIncidentFace P' e) ≤ 4) := by
  have hv := BDL26BoundedValence.rz_boundedValence P A4 R S h
  exact ⟨hv, xqIncidentFace_card_le_four _ hv, qzIncidentFace_card_le_four _ hv⟩
end QEC.Coding.BDL26ReplacementEmbedding
