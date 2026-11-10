-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.TriangleWidthAtLeast.swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:38:15.154716+00:00
-- url     : https://prove2.me/submissions/12d6d3c7-94ab-4b24-8f3a-7baab4477896

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
namespace TriangleWidthAtLeast
theorem _root_.solution {b c : E} {delta : ℝ}
    (h : TriangleWidthAtLeast b c delta) : TriangleWidthAtLeast c b delta := by
  refine ⟨h.2.1, h.1, ?_⟩
  intro t ht0 ht1
  have he : (1 - t) • c + t • b = (1 - (1 - t)) • b + (1 - t) • c := by module
  rw [he]
  exact h.2.2 (1 - t) (by linarith) (by linarith)
end TriangleWidthAtLeast
end QEC.Coding.BDL26ReplacementEmbedding
