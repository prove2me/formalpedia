-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.actualRXHits_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:21:24.876653+00:00
-- url     : https://prove2.me/submissions/af3bec7a-8649-4c9b-a9cc-2a2eea45ce27

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_actualFlatHits_card_le_three_mul_positive
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_actualRXHits_card_eq_flat
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_actualPositiveHits_card_le
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width tPrime : ℝ}
    (hlower : 0 < lower) (hwidth : 0 < width)
    (hgeo : IncomingFaceGeometry P S J lower width) (center : E)
    (hincoming : ((familyHits (oldTriangleImage P J) (Metric.closedBall center 1)).card : ℝ) ≤ tPrime) :
    ((familyHits (rxFaceImage P S J) (Metric.closedBall center 1)).card : ℝ) ≤
      48 * Real.pi * tPrime * S.ell ^ 2 / (lower * width) := by
  rw [actualRXHits_card_eq_flat]
  have hcharge : ((familyHits (actualFlatImage P S J) (Metric.closedBall center 1)).card : ℝ) ≤
      3 * ((familyHits (fun p : P.Face × PositiveCell S =>
        actualFlatImage P S J (p.1, .inl p.2)) (Metric.closedBall center 1)).card : ℝ) := by
    exact_mod_cast actualFlatHits_card_le_three_mul_positive P S J (Metric.closedBall center 1)
  have hpositive := actualPositiveHits_card_le P S J hlower hwidth hgeo center
  have hbound := mul_le_mul_of_nonneg_right hincoming
    (show 0 ≤ 16 * Real.pi * (S.ell : ℝ) ^ 2 / (lower * width) by positivity)
  calc
    _ ≤ 3 * ((familyHits (fun p : P.Face × PositiveCell S =>
        actualFlatImage P S J (p.1, .inl p.2)) (Metric.closedBall center 1)).card : ℝ) := hcharge
    _ ≤ 3 * (tPrime * (16 * Real.pi * (S.ell : ℝ) ^ 2 / (lower * width))) :=
      mul_le_mul_of_nonneg_left (hpositive.trans hbound) (by norm_num)
    _ = 48 * Real.pi * tPrime * S.ell ^ 2 / (lower * width) := by ring
end QEC.Coding.BDL26ReplacementEmbedding
