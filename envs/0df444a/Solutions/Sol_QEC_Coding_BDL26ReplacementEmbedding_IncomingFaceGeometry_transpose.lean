-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.IncomingFaceGeometry.transpose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:25:43.119573+00:00
-- url     : https://prove2.me/submissions/59c9e44c-ba41-4051-b80d-3fe9b8c87a45

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

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
namespace IncomingFaceGeometry
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width : ℝ} (h : IncomingFaceGeometry P S J lower width) :
    IncomingFaceGeometry (transposePresentation P) S (transposePointMap P J) lower width := by
  constructor
  · intro f side
    change lower ≤ ‖J (.q (P.faceQ f side)) - J (.z (P.faceZ f))‖
    rw [norm_sub_rev]
    exact h.opposite_lower f side
  · intro f
    change lower ≤ ‖J (.x (P.faceX f)) - J (.z (P.faceZ f))‖
    rw [norm_sub_rev]
    exact h.diagonal_lower f
  · intro f side
    change lower ≤ ‖J (.x (P.faceX f)) - J (.q (P.faceQ f side))‖
    rw [norm_sub_rev]
    exact h.side_lower f side
  · intro f side
    change ‖J (.q (P.faceQ f side)) - J (.z (P.faceZ f))‖ ≤ S.ell
    rw [norm_sub_rev]
    exact h.opposite_upper f side
  · intro f
    change ‖J (.x (P.faceX f)) - J (.z (P.faceZ f))‖ ≤ S.ell
    rw [norm_sub_rev]
    exact h.diagonal_upper f
  · intro f side
    change ‖J (.x (P.faceX f)) - J (.q (P.faceQ f side))‖ ≤ S.ell
    rw [norm_sub_rev]
    exact h.side_upper f side
  · intro f side
    change TriangleWidthAtLeast (J (.q (P.faceQ f side)) - J (.z (P.faceZ f)))
      (J (.x (P.faceX f)) - J (.z (P.faceZ f))) width
    have ht := (h.triangle_width f side).transpose
    have hb : (J (.q (P.faceQ f side)) - J (.x (P.faceX f))) -
        (J (.z (P.faceZ f)) - J (.x (P.faceX f))) =
        J (.q (P.faceQ f side)) - J (.z (P.faceZ f)) := by abel
    have hc : -(J (.z (P.faceZ f)) - J (.x (P.faceX f))) =
        J (.x (P.faceX f)) - J (.z (P.faceZ f)) := by abel
    rw [hb, hc] at ht
    exact ht
end IncomingFaceGeometry
end QEC.Coding.BDL26ReplacementEmbedding
