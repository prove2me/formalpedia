-- Prove2me | solution 1 for SZ.Slice.W_eq_residual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:26:00.050873+00:00
-- url     : https://prove2.me/submissions/10b2b055-a7bc-410f-bf39-ab125912ffeb

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
import Theorems.Thm_SZ_Slice_three_le_cast
import Theorems.Thm_SZ_Slice_W_zero
import Theorems.Thm_SZ_Slice_W_succ
import Theorems.Thm_SZ_Slice_val_pick_W
import Theorems.Thm_SZ_digitSum_succ
import Theorems.Thm_SZ_digitSum_zero


set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)
variable {S}
namespace SZ.Slice
theorem _root_.solution (S : Slice) (σ : ℝ) (k : ℕ) :
    S.W ((S.m : ℝ) * σ) k = (S.m : ℝ) ^ (k + 1) *
      (σ - digitSum S.m (S.dA ((S.m : ℝ) * σ)) k
         - S.sq * digitSum S.m (S.dB ((S.m : ℝ) * σ)) k) := by
  have hm : (0 : ℝ) < (S.m : ℝ) := by have := S.three_le_cast; linarith
  induction k with
  | zero => rw [W_zero, digitSum_zero, digitSum_zero]; ring
  | succ k ih =>
    rw [W_succ, val_pick_W, ih, digitSum_succ, digitSum_succ]
    have hne : ((S.m : ℝ)) ^ (k + 1) ≠ 0 := by positivity
    field_simp
    ring
end SZ.Slice
