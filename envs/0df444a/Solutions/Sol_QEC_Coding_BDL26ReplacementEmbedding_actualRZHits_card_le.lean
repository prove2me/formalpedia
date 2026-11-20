-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.actualRZHits_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:27:22.354439+00:00
-- url     : https://prove2.me/submissions/d56607f5-befb-4fec-b261-2defd97aad66

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_TriangleWidthAtLeast_transpose
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_actualRXHits_card_le
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_oldTriangleImage_transpose
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_IncomingFaceGeometry_transpose
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_actualRZHits_card_eq_transpose

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) {lower width tPrime : ℝ}
    (hlower : 0 < lower) (hwidth : 0 < width)
    (hgeo : IncomingFaceGeometry P S J lower width) (center : E)
    (hincoming : ((familyHits (oldTriangleImage P J) (Metric.closedBall center 1)).card : ℝ) ≤ tPrime) :
    ((familyHits (rzFaceImage P A S J) (Metric.closedBall center 1)).card : ℝ) ≤
      48 * Real.pi * tPrime * S.ell ^ 2 / (lower * width) := by
  rw [actualRZHits_card_eq_transpose]
  apply actualRXHits_card_le (transposePresentation P) S (transposePointMap P J)
    hlower hwidth (IncomingFaceGeometry.transpose P S J hgeo) center
  have he : oldTriangleImage (transposePresentation P) (transposePointMap P J) =
      oldTriangleImage P J := by
    funext p
    exact oldTriangleImage_transpose P J p.1 p.2
  rw [he]
  exact hincoming
end QEC.Coding.BDL26ReplacementEmbedding
