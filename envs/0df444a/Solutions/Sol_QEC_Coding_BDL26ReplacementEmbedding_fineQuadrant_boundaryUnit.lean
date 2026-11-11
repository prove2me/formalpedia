-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.fineQuadrant_boundaryUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:32:35.45391+00:00
-- url     : https://prove2.me/submissions/6eb53025-a976-4162-ad56-a535d6923770

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_faceFineCorner_horizontal_dist
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_faceFineCorner_vertical_dist

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width : ℝ} (hgeo : IncomingFaceGeometry P S J lower width)
    (f : P.Face) (m n : ℤ) (a b : BDL26FiniteTannerSquare.Two) :
    BoundaryUnit (faceFineCorner P S J f m n a b)
      (faceFineCorner P S J f m n (1 - a) b)
      (faceFineCorner P S J f m n a (1 - b))
      (faceFineCorner P S J f m n (1 - a) (1 - b)) := by
  exact ⟨faceFineCorner_horizontal_dist P S J hgeo f m n a b,
    faceFineCorner_vertical_dist P S J hgeo f m n a b,
    faceFineCorner_vertical_dist P S J hgeo f m n (1 - a) b,
    faceFineCorner_horizontal_dist P S J hgeo f m n a (1 - b)⟩
end QEC.Coding.BDL26ReplacementEmbedding
