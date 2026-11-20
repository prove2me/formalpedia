-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rx_constructed_localMap_rounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:36:53.106847+00:00
-- url     : https://prove2.me/submissions/4cf61563-d9f8-4d17-b7c0-589014967d38

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_actualRXHits_card_le_rounded
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rxXQ_edge_dist
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rxQZ_edge_dist

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {alpha alpha2 gamma lambda tPrime : ℝ}
    (hlambda : 0 < lambda) (hgamma : 0 < gamma) (halpha2 : 1 < alpha2)
    (htPrime : 0 ≤ tPrime) (hscale : 13 ≤ (2 * alpha + 1) * lambda)
    (hround : (S.ell : ℝ) ≤ (2 * alpha + 1) * lambda + 2)
    (hgeo : IncomingFaceGeometry P S J ((alpha2 - 1) * lambda) (gamma * lambda))
    (hincoming : ∀ center,
      ((familyHits (oldTriangleImage P J) (Metric.closedBall center 1)).card : ℝ) ≤ tPrime) :
    IsBoundedDensityLocalMap (rxReplacementPresentation P S) (rxVertexPoint P S J)
      (64 * Real.pi * tPrime * (2 * alpha + 1) ^ 2 / (gamma * (alpha2 - 1))) := by
  refine ⟨fun x q h => rxXQ_edge_dist P S J hgeo x q h,
    fun q z h => rxQZ_edge_dist P S J hgeo q z h, ?_⟩
  intro center
  change ((familyHits (rxFaceImage P S J) (Metric.closedBall center 1)).card : ℝ) ≤ _
  exact actualRXHits_card_le_rounded P S J hlambda hgamma halpha2 htPrime hscale hround
    hgeo center (hincoming center)
end QEC.Coding.BDL26ReplacementEmbedding
