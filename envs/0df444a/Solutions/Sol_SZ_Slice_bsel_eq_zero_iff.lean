-- Prove2me | solution 1 for SZ.Slice.bsel_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:25:37.617805+00:00
-- url     : https://prove2.me/submissions/e79e89da-9ffa-4f1a-8042-cbd1bfc0da94

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
import Theorems.Thm_SZ_Slice_p_pos
import Theorems.Thm_SZ_Slice_p_sq_pos
import Theorems.Thm_SZ_Slice_e_pos

set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)
namespace SZ.Slice
theorem _root_.solution {w : ℝ} (h0 : 0 ≤ w) : S.bsel w = 0 ↔ w < (S.p : ℝ) * S.sq := by
  have hs : (0 : ℝ) < (S.p : ℝ) * S.sq := S.p_sq_pos
  constructor
  · intro h
    by_contra hge
    push Not at hge
    have h1 : (1 : ℝ) ≤ w / ((S.p : ℝ) * S.sq) := (le_div_iff₀ hs).mpr (by linarith)
    have h2 : (1 : ℤ) ≤ ⌊w / ((S.p : ℝ) * S.sq)⌋ := Int.le_floor.mpr (by exact_mod_cast h1)
    have h3 : S.p ≤ S.p * ⌊w / ((S.p : ℝ) * S.sq)⌋ :=
      le_mul_of_one_le_right S.p_pos.le h2
    have h4 := S.p_le_e
    have h5 := S.p_pos
    rw [bsel] at h
    set t : ℤ := S.p * ⌊w / ((S.p : ℝ) * S.sq)⌋
    omega
  · intro h
    have h1 : w / ((S.p : ℝ) * S.sq) < 1 := (div_lt_one hs).mpr h
    have h2 : ⌊w / ((S.p : ℝ) * S.sq)⌋ = 0 :=
      Int.floor_eq_zero_iff.mpr ⟨div_nonneg h0 hs.le, h1⟩
    rw [bsel, h2, mul_zero]
    exact min_eq_right S.e_pos.le
end SZ.Slice
