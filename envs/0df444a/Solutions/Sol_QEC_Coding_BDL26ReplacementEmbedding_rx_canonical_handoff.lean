-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rx_canonical_handoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:46:45.23024+00:00
-- url     : https://prove2.me/submissions/669cb36e-4fec-4867-9cd6-663648a82630

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_canonical_replacement_scale_bounds
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rx_constructed_localMap_rounded
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rx_constructed_degrees

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
open BDL26BoundedValence
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (hvalence : BoundedValence P) (J : Vertex P → E)
    {alpha alpha2 gamma lambda tPrime : ℝ}
    (hlambda : 0 < lambda) (hgamma : 0 < gamma) (halpha2 : 1 < alpha2)
    (htPrime : 0 ≤ tPrime) (hscale : 13 ≤ (2 * alpha + 1) * lambda)
    (hgeo : IncomingFaceGeometry P (replacementScale alpha lambda hscale) J
      ((alpha2 - 1) * lambda) (gamma * lambda))
    (hincoming : ∀ center,
      ((familyHits (oldTriangleImage P J) (Metric.closedBall center 1)).card : ℝ) ≤ tPrime) :
    let S := replacementScale alpha lambda hscale
    let Pnext := rxReplacementPresentation P S
    BoundedValence Pnext ∧
      (∀ e : XQEdge Pnext, Fintype.card (XQIncidentFace Pnext e) ≤ 4) ∧
      (∀ e : QZEdge Pnext, Fintype.card (QZIncidentFace Pnext e) ≤ 4) ∧
      IsBoundedDensityLocalMap Pnext (rxVertexPoint P S J)
        (64 * Real.pi * tPrime * (2 * alpha + 1) ^ 2 / (gamma * (alpha2 - 1))) := by
  let S := replacementScale alpha lambda hscale
  have hd := rx_constructed_degrees P A4 R S hvalence
  refine ⟨hd.1, hd.2.1, hd.2.2, ?_⟩
  exact rx_constructed_localMap_rounded P S J hlambda hgamma halpha2 htPrime hscale
    (canonical_replacement_scale_bounds hscale).2 hgeo hincoming
end QEC.Coding.BDL26ReplacementEmbedding
