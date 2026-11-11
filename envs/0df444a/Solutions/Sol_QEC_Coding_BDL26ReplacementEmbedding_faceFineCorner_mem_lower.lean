-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.faceFineCorner_mem_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:05:48.909405+00:00
-- url     : https://prove2.me/submissions/b525dd90-58cf-4b8d-b8db-743c0efd0892

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_foldedSquare_mem_lower_triangle

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (m n : ℤ) (a b : BDL26FiniteTannerSquare.Two)
    (hu : m + a.val ≤ (S.ell : ℤ)) (hv : 0 ≤ n + b.val)
    (hvu : n + b.val ≤ m + a.val) :
    faceFineCorner P S J f m n a b ∈ oldTriangleImage P J (f, 0) := by
  have hell : (0 : ℝ) < S.ell := by
    exact_mod_cast (show 0 < S.ell by have := S.three_le; omega)
  exact foldedSquare_mem_lower_triangle _ _ _ _
    ((div_le_one hell).2 (by exact_mod_cast hu))
    (div_nonneg (by exact_mod_cast hv) hell.le)
    ((div_le_div_iff_of_pos_right hell).2 (by exact_mod_cast hvu))
end QEC.Coding.BDL26ReplacementEmbedding
