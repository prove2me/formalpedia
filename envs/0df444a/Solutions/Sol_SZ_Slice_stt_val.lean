-- Prove2me | solution 1 for SZ.Slice.stt_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:27:29.566432+00:00
-- url     : https://prove2.me/submissions/dd7b4f87-f2cd-41e5-9ec6-032415bca1de

import Definitions.Def_SZ_Slice
import Mathlib.Tactic.Push
import Definitions.Def_SZ_SliceHygiene
import Theorems.Thm_SZ_Slice_M_eq_one
import Theorems.Thm_SZ_Slice_stt_zero
import Theorems.Thm_SZ_Slice_stt_succ
import Theorems.Thm_SZ_Slice_W_succ
import Theorems.Thm_SZ_Slice_W_zero
import Theorems.Thm_SZ_Slice_val_pick_W
import Theorems.Thm_SZ_Slice_w0_def


set_option autoImplicit false
open SZ
open SZ.Slice
variable {S : Slice}
namespace SZ.Slice
theorem _root_.solution (he : S.e = (S.m : ℤ) - 1) (j k₀ : ℤ) (k : ℕ) :
    S.W (S.w0 j k₀) k = ((stt S j k₀ k).1 : ℝ) + ((stt S j k₀ k).2 : ℝ) * S.sq := by
  induction k with
  | zero =>
    rw [W_zero, stt_zero, w0_def, sigma, M_eq_one he]
    push_cast
    ring
  | succ k ih =>
    rw [W_succ, val_pick_W, ih, stt_succ]
    push_cast
    ring
end SZ.Slice
