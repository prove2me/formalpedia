-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.leastOddScaleAbove_le_add_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:31:36.537095+00:00
-- url     : https://prove2.me/submissions/8ef8e6b7-d348-4b57-af65-f874cc8c7f98

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
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (threshold : ℝ) (hone : 1 ≤ threshold) :
    ((leastOddScaleAbove threshold hone).ell : ℝ) ≤ threshold + 2 := by
  have hn : leastOddAbove ⌊threshold⌋₊ ≤ ⌊threshold⌋₊ + 2 := by
    unfold leastOddAbove
    omega
  have hf : (⌊threshold⌋₊ : ℝ) ≤ threshold := Nat.floor_le (by linarith)
  calc
    ((leastOddScaleAbove threshold hone).ell : ℝ) ≤ (⌊threshold⌋₊ : ℝ) + 2 := by
      exact_mod_cast hn
    _ ≤ threshold + 2 := by linarith
end QEC.Coding.BDL26ReplacementEmbedding
