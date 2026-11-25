-- Prove2me | solution 1 for SZ.Slice.le_asel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:25:45.619541+00:00
-- url     : https://prove2.me/submissions/4616b0f4-a5cb-4624-ab4f-a4a95e72c122

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
import Theorems.Thm_SZ_Slice_p_cast_pos

set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)
namespace SZ.Slice
theorem _root_.solution (w : ℝ) : w - (S.bsel w : ℝ) * S.sq - S.U ≤ (S.asel w : ℝ) := by
  have hp := S.p_cast_pos
  have hge : (w - (S.bsel w : ℝ) * S.sq - S.U) / (S.p : ℝ)
      ≤ ((max 0 ⌈(w - (S.bsel w : ℝ) * S.sq - S.U) / (S.p : ℝ)⌉ : ℤ) : ℝ) := by
    refine le_trans (Int.le_ceil _) ?_
    exact_mod_cast le_max_right (0 : ℤ) ⌈(w - (S.bsel w : ℝ) * S.sq - S.U) / (S.p : ℝ)⌉
  have hmul := mul_le_mul_of_nonneg_left hge hp.le
  have hcancel : (S.p : ℝ) * ((w - (S.bsel w : ℝ) * S.sq - S.U) / (S.p : ℝ))
      = w - (S.bsel w : ℝ) * S.sq - S.U := by field_simp
  rw [hcancel] at hmul
  rw [asel]
  push_cast at hmul ⊢
  linarith
end SZ.Slice
