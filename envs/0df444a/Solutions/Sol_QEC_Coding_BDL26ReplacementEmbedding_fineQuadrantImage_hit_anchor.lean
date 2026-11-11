-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.fineQuadrantImage_hit_anchor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:23:06.657739+00:00
-- url     : https://prove2.me/submissions/9f06a33b-fba0-42f3-ae03-add85cae468b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_triangle_hit_anchor_bound
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_faceFineCorner_dist_anchor

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (m n : ℤ) (a b : BDL26FiniteTannerSquare.Two)
    (h₀ : ‖J (.q (P.faceQ f 0)) - J (.x (P.faceX f))‖ ≤ S.ell)
    (h₁ : ‖J (.q (P.faceQ f 1)) - J (.x (P.faceX f))‖ ≤ S.ell)
    (hz : ‖J (.z (P.faceZ f)) - J (.x (P.faceX f))‖ ≤ S.ell)
    (hz₀ : ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f 0))‖ ≤ S.ell)
    (hz₁ : ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f 1))‖ ≤ S.ell)
    (center : E)
    (hhit : (fineQuadrantImage P S J f m n a b ∩ Metric.closedBall center 1).Nonempty) :
    dist (faceFineAnchor P S J f m n) center ≤ 2 := by
  obtain ⟨w, hw, hball⟩ := hhit
  have hc (u v : BDL26FiniteTannerSquare.Two) :=
    faceFineCorner_dist_anchor P S J f m n u v h₀ h₁ hz hz₀ hz₁
  rcases hw with hw | hw
  · exact triangle_hit_anchor_bound _ _ _ _ _
      (hc a b) (hc (1 - a) b) (hc (1 - a) (1 - b)) ⟨w, hw, hball⟩
  · exact triangle_hit_anchor_bound _ _ _ _ _
      (hc a b) (hc (1 - a) (1 - b)) (hc a (1 - b)) ⟨w, hw, hball⟩
end QEC.Coding.BDL26ReplacementEmbedding
