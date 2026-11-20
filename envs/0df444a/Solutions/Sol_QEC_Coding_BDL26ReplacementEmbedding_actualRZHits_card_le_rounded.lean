-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.actualRZHits_card_le_rounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:36:49.830507+00:00
-- url     : https://prove2.me/submissions/ada3f9b0-344c-4651-9790-d9c3ca0b79fd

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
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_actualRXHits_card_le_rounded
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
    (S : OddScale) (J : Vertex P → E) {alpha alpha2 gamma lambda tPrime : ℝ}
    (hlambda : 0 < lambda) (hgamma : 0 < gamma) (halpha2 : 1 < alpha2)
    (htPrime : 0 ≤ tPrime) (hscale : 13 ≤ (2 * alpha + 1) * lambda)
    (hround : (S.ell : ℝ) ≤ (2 * alpha + 1) * lambda + 2)
    (hgeo : IncomingFaceGeometry P S J ((alpha2 - 1) * lambda) (gamma * lambda))
    (center : E)
    (hincoming : ((familyHits (oldTriangleImage P J) (Metric.closedBall center 1)).card : ℝ) ≤ tPrime) :
    ((familyHits (rzFaceImage P A S J) (Metric.closedBall center 1)).card : ℝ) ≤
      64 * Real.pi * tPrime * (2 * alpha + 1) ^ 2 / (gamma * (alpha2 - 1)) := by
  rw [actualRZHits_card_eq_transpose]
  apply actualRXHits_card_le_rounded (transposePresentation P) S (transposePointMap P J)
    hlambda hgamma halpha2 htPrime hscale hround
    (IncomingFaceGeometry.transpose P S J hgeo) center
  have he : oldTriangleImage (transposePresentation P) (transposePointMap P J) =
      oldTriangleImage P J := by
    funext p
    exact oldTriangleImage_transpose P J p.1 p.2
  rw [he]
  exact hincoming
end QEC.Coding.BDL26ReplacementEmbedding
