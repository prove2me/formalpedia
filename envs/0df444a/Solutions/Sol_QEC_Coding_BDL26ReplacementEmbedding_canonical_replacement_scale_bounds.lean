-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.canonical_replacement_scale_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:36:27.519039+00:00
-- url     : https://prove2.me/submissions/139764c8-5341-493c-a88c-c52df77c4d76

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_leastOddScaleAbove_le_add_two
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_leastOddScaleAbove_gt


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution {alpha lambda : ℝ}
    (hscale : 13 ≤ (2 * alpha + 1) * lambda) :
    let S := leastOddScaleAbove ((2 * alpha + 1) * lambda) (by linarith)
    (2 * alpha + 1) * lambda < (S.ell : ℝ) ∧
      (S.ell : ℝ) ≤ (2 * alpha + 1) * lambda + 2 := by
  exact ⟨leastOddScaleAbove_gt _ _, leastOddScaleAbove_le_add_two _ _⟩
end QEC.Coding.BDL26ReplacementEmbedding
