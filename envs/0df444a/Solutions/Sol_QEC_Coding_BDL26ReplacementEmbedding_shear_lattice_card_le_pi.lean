-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.shear_lattice_card_le_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:56:31.102311+00:00
-- url     : https://prove2.me/submissions/2fffe4ce-4671-4327-a43f-a097c784c5d5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_shear_lattice_card_le

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open BDL26FiniteTannerSquare
open scoped BigOperators
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (s : Finset (ℤ × ℤ)) {a h c x y : ℝ}
    (ha : 0 < a) (hh : 0 < h) (ha1 : a ≤ 1) (hh1 : h ≤ 1)
    (hx : ∀ p ∈ s, |a * (p.1 : ℝ) + c * (p.2 : ℝ) - x| ≤ 2)
    (hy : ∀ p ∈ s, |h * (p.2 : ℝ) - y| ≤ 2) :
    (s.card : ℝ) ≤ 8 * Real.pi / (a * h) := by
  have ha5 : 4 / a + 1 ≤ 5 / a := by
    apply (le_div_iff₀ ha).2
    rw [add_mul, div_mul_cancel₀ _ ha.ne', one_mul]
    linarith
  have hh5 : 4 / h + 1 ≤ 5 / h := by
    apply (le_div_iff₀ hh).2
    rw [add_mul, div_mul_cancel₀ _ hh.ne', one_mul]
    linarith
  calc
    (s.card : ℝ) ≤ (4 / h + 1) * (4 / a + 1) :=
      shear_lattice_card_le s ha hh hx hy
    _ ≤ (5 / h) * (5 / a) := mul_le_mul hh5 ha5 (by positivity) (by positivity)
    _ = 25 / (a * h) := by ring
    _ ≤ 8 * Real.pi / (a * h) :=
      (div_le_div_iff_of_pos_right (mul_pos ha hh)).2 (by linarith [Real.pi_gt_d2])
end QEC.Coding.BDL26ReplacementEmbedding
