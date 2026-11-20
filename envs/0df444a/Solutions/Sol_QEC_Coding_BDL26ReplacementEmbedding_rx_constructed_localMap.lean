-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rx_constructed_localMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:27:29.024187+00:00
-- url     : https://prove2.me/submissions/8601eb62-9ec9-4468-be65-e2e286f14026

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_actualRXHits_card_le
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rxXQ_edge_dist
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rxQZ_edge_dist

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width tPrime : ℝ} (hlower : 0 < lower) (hwidth : 0 < width)
    (hgeo : IncomingFaceGeometry P S J lower width)
    (hincoming : ∀ center,
      ((familyHits (oldTriangleImage P J) (Metric.closedBall center 1)).card : ℝ) ≤ tPrime) :
    IsBoundedDensityLocalMap (rxReplacementPresentation P S) (rxVertexPoint P S J)
      (48 * Real.pi * tPrime * S.ell ^ 2 / (lower * width)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x q h
    exact rxXQ_edge_dist P S J hgeo x q h
  · intro q z h
    exact rxQZ_edge_dist P S J hgeo q z h
  · intro center
    have he : tannerFaceImage (rxReplacementPresentation P S) (rxVertexPoint P S J) =
        rxFaceImage P S J := rfl
    rw [he]
    exact actualRXHits_card_le P S J hlower hwidth hgeo center (hincoming center)
end QEC.Coding.BDL26ReplacementEmbedding
