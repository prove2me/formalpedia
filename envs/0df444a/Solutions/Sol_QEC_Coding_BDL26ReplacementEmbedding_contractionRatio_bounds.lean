-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.contractionRatio_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:53:19.187879+00:00
-- url     : https://prove2.me/submissions/462d4cc9-2bf1-4118-8448-e24a4112ebcf

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
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (S : OddScale) :
    0 ≤ contractionRatio S ∧ contractionRatio S < 1 := by
  have he : (0 : ℝ) < S.ell := by exact_mod_cast (show 0 < S.ell by have := S.three_le; omega)
  have ho : 2 * (S.half : ℝ) + 1 = S.ell := by exact_mod_cast S.two_half_add_one
  constructor
  · exact div_nonneg (by positivity) he.le
  · apply (div_lt_one he).2
    linarith
end QEC.Coding.BDL26ReplacementEmbedding
