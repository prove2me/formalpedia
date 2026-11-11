-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.actualPositive_hit_anchor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:34:49.557534+00:00
-- url     : https://prove2.me/submissions/a296667c-a0a5-4ee3-804d-92bc654182f3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_actualFlatImage_raw_positive
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_fineQuadrantImage_hit_anchor
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rawPositiveFace_image_fine

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (c : PositiveCell S)
    (h₀ : ‖J (.q (P.faceQ f 0)) - J (.x (P.faceX f))‖ ≤ S.ell)
    (h₁ : ‖J (.q (P.faceQ f 1)) - J (.x (P.faceX f))‖ ≤ S.ell)
    (hz : ‖J (.z (P.faceZ f)) - J (.x (P.faceX f))‖ ≤ S.ell)
    (hz₀ : ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f 0))‖ ≤ S.ell)
    (hz₁ : ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f 1))‖ ≤ S.ell)
    (center : E)
    (hhit : (actualFlatImage P S J (f, .inl c) ∩ Metric.closedBall center 1).Nonempty) :
    dist (faceFineAnchor P S J f c.2.1.val c.2.2.val) center ≤ 2 := by
  obtain ⟨raw, rfl⟩ := (rawPositiveCellEquiv S).surjective c
  rw [actualFlatImage_raw_positive, rawPositiveFace_image_fine] at hhit
  exact fineQuadrantImage_hit_anchor P S J f _ _ _ _ h₀ h₁ hz hz₀ hz₁ center hhit
end QEC.Coding.BDL26ReplacementEmbedding
