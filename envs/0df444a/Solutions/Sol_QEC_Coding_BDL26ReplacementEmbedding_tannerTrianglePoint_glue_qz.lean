-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.tannerTrianglePoint_glue_qz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:47:44.896234+00:00
-- url     : https://prove2.me/submissions/72e40884-179a-4f3c-9e2d-8c54aff36e42

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_tannerTrianglePoint_qz

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → E)
    (f g : P.Face) (i j : BDL26FiniteTannerSquare.Two)
    (h : faceQZEdge P f i = faceQZEdge P g j) (t : ℝ) :
    tannerTrianglePoint P J f i (1 - t) t = tannerTrianglePoint P J g j (1 - t) t := by
  rw [tannerTrianglePoint_qz, tannerTrianglePoint_qz, h]
end QEC.Coding.BDL26ReplacementEmbedding
