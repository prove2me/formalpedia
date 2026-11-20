-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.actualRXHits_card_le_rounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:27:18.898187+00:00
-- url     : https://prove2.me/submissions/aa05d775-8e17-4b26-95dd-21df7a666526

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
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rounded_density_handoff


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
    (center : E)
    (hincoming : ((familyHits (oldTriangleImage P J) (Metric.closedBall center 1)).card : ℝ) ≤ tPrime) :
    ((familyHits (rxFaceImage P S J) (Metric.closedBall center 1)).card : ℝ) ≤
      64 * Real.pi * tPrime * (2 * alpha + 1) ^ 2 / (gamma * (alpha2 - 1)) := by
  have hd := actualRXHits_card_le P S J (mul_pos (sub_pos.mpr halpha2) hlambda)
    (mul_pos hgamma hlambda) hgeo center hincoming
  have hs := rounded_density_handoff hscale (show 0 ≤ (S.ell : ℝ) by positivity) hround
    (show 0 ≤ Real.pi * tPrime / (((alpha2 - 1) * lambda) * (gamma * lambda)) by positivity)
  calc
    _ ≤ 48 * Real.pi * tPrime * S.ell ^ 2 /
        (((alpha2 - 1) * lambda) * (gamma * lambda)) := hd
    _ = 48 * (Real.pi * tPrime / (((alpha2 - 1) * lambda) * (gamma * lambda))) * S.ell ^ 2 := by ring
    _ ≤ 64 * (Real.pi * tPrime / (((alpha2 - 1) * lambda) * (gamma * lambda))) *
        ((2 * alpha + 1) * lambda) ^ 2 := hs
    _ = _ := by
      have hlambda0 : lambda ≠ 0 := ne_of_gt hlambda
      have hgamma0 : gamma ≠ 0 := ne_of_gt hgamma
      have ha : alpha2 - 1 ≠ 0 := ne_of_gt (sub_pos.mpr halpha2)
      field_simp
      <;> ring
end QEC.Coding.BDL26ReplacementEmbedding
