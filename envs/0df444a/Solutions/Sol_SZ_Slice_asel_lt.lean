-- Prove2me | solution 1 for SZ.Slice.asel_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:17:20.391433+00:00
-- url     : https://prove2.me/submissions/76e4b55c-87ac-40ce-a7e4-dfda75fcbcde

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
theorem _root_.solution {w : ℝ} (h : S.U < w - (S.bsel w : ℝ) * S.sq) :
    (S.asel w : ℝ) < w - (S.bsel w : ℝ) * S.sq - S.U + (S.p : ℝ) := by
  have hp := S.p_cast_pos
  have hpos : (0 : ℝ) < (w - (S.bsel w : ℝ) * S.sq - S.U) / (S.p : ℝ) :=
    div_pos (by linarith) hp
  have hc : (0 : ℤ) < ⌈(w - (S.bsel w : ℝ) * S.sq - S.U) / (S.p : ℝ)⌉ :=
    Int.lt_ceil.mpr (by push_cast; exact hpos)
  have hmax : max 0 ⌈(w - (S.bsel w : ℝ) * S.sq - S.U) / (S.p : ℝ)⌉
      = ⌈(w - (S.bsel w : ℝ) * S.sq - S.U) / (S.p : ℝ)⌉ := max_eq_right (le_of_lt hc)
  have hlt : (⌈(w - (S.bsel w : ℝ) * S.sq - S.U) / (S.p : ℝ)⌉ : ℝ)
      < (w - (S.bsel w : ℝ) * S.sq - S.U) / (S.p : ℝ) + 1 := Int.ceil_lt_add_one _
  have hmul := mul_lt_mul_of_pos_left hlt hp
  have hcancel : (S.p : ℝ) * ((w - (S.bsel w : ℝ) * S.sq - S.U) / (S.p : ℝ) + 1)
      = w - (S.bsel w : ℝ) * S.sq - S.U + (S.p : ℝ) := by
    field_simp
  rw [hcancel] at hmul
  rw [asel, hmax]
  push_cast
  linarith
end SZ.Slice
