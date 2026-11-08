-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.int_affine_interval_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:12:12.710061+00:00
-- url     : https://prove2.me/submissions/7a771f39-97a8-4f03-acb5-86b62190f9e3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_int_interval_card_le

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open BDL26FiniteTannerSquare
open scoped BigOperators
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (s : Finset ℤ) {spacing center radius : ℝ}
    (hspacing : 0 < spacing) (hradius : 0 ≤ radius)
    (hmem : ∀ z ∈ s, |spacing * (z : ℝ) - center| ≤ radius) :
    (s.card : ℝ) ≤ 2 * radius / spacing + 1 := by
  have hab : (center - radius) / spacing ≤ (center + radius) / spacing :=
    (div_le_div_iff_of_pos_right hspacing).2 (by linarith)
  have hc := int_interval_card_le s hab (fun z hz => by
    have ha := abs_le.mp (hmem z hz)
    constructor
    · apply (div_le_iff₀ hspacing).2
      nlinarith
    · apply (le_div_iff₀ hspacing).2
      nlinarith)
  convert hc using 1 <;> field_simp <;> ring
end QEC.Coding.BDL26ReplacementEmbedding
