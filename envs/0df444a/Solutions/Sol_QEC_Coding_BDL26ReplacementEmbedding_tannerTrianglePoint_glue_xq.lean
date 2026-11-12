-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.tannerTrianglePoint_glue_xq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:47:29.684526+00:00
-- url     : https://prove2.me/submissions/92d818f3-5ff9-4a19-be31-bea1fcdef17f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_tannerTrianglePoint_xq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → E)
    (f g : P.Face) (i j : BDL26FiniteTannerSquare.Two)
    (h : faceXQEdge P f i = faceXQEdge P g j) (t : ℝ) :
    tannerTrianglePoint P J f i t 0 = tannerTrianglePoint P J g j t 0 := by
  rw [tannerTrianglePoint_xq, tannerTrianglePoint_xq, h]
end QEC.Coding.BDL26ReplacementEmbedding
