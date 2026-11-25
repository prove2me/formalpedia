-- Prove2me | solution 1 for SZ.Slice.bsel_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:25:28.684204+00:00
-- url     : https://prove2.me/submissions/5bc36e1f-3ba6-437c-bd29-f424c199062f

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
import Theorems.Thm_SZ_Slice_sq_pos
import Theorems.Thm_SZ_Slice_p_sq_pos

set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)
namespace SZ.Slice
theorem _root_.solution (w : ℝ) : (S.bsel w : ℝ) * S.sq ≤ w := by
  have hs : (0 : ℝ) < (S.p : ℝ) * S.sq := S.p_sq_pos
  have hne : ((S.p : ℝ) * S.sq) ≠ 0 := ne_of_gt hs
  have hcancel : ((S.p : ℝ) * S.sq) * (w / ((S.p : ℝ) * S.sq)) = w := by
    rw [mul_comm, div_mul_cancel₀ _ hne]
  have h1 : ((S.p : ℝ) * S.sq) * (⌊w / ((S.p : ℝ) * S.sq)⌋ : ℝ) ≤ w := by
    have := mul_le_mul_of_nonneg_left (Int.floor_le (w / ((S.p : ℝ) * S.sq))) hs.le
    rw [hcancel] at this
    exact this
  have h2 : (S.bsel w : ℝ) ≤ ((S.p * ⌊w / ((S.p : ℝ) * S.sq)⌋ : ℤ) : ℝ) := by
    have : S.bsel w ≤ S.p * ⌊w / ((S.p : ℝ) * S.sq)⌋ := min_le_right _ _
    exact_mod_cast this
  push_cast at h2
  nlinarith [S.sq_pos]
end SZ.Slice
