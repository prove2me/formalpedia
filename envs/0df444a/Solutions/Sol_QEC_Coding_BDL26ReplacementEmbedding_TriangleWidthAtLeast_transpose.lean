-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.TriangleWidthAtLeast.transpose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:20:06.997727+00:00
-- url     : https://prove2.me/submissions/3bb33a0d-c365-48ea-90e0-54a038acd041

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_TriangleWidthAtLeast_swap
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_TriangleWidthAtLeast_rebase

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
namespace TriangleWidthAtLeast
theorem _root_.solution {b c : E} {delta : ℝ}
    (h : TriangleWidthAtLeast b c delta) : TriangleWidthAtLeast (b - c) (-c) delta :=
  h.swap.rebase
end TriangleWidthAtLeast
end QEC.Coding.BDL26ReplacementEmbedding
