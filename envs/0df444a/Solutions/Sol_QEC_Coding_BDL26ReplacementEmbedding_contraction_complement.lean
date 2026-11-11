-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.contraction_complement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:26:43.431204+00:00
-- url     : https://prove2.me/submissions/6c17fe64-6e52-460a-b209-03cada7551da

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_OddScale_two_half_add_one


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (S : OddScale) : 1 - contractionRatio S = 1 / S.ell := by
  have h : 2 * (S.half : ℝ) + 1 = S.ell := by exact_mod_cast S.two_half_add_one
  have he : (S.ell : ℝ) ≠ 0 := by exact_mod_cast (show S.ell ≠ 0 by have := S.three_le; omega)
  unfold contractionRatio
  field_simp
  linarith
end QEC.Coding.BDL26ReplacementEmbedding
