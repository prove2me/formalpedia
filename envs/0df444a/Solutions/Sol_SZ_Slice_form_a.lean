-- Prove2me | solution 1 for SZ.Slice.form_a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:26:56.53368+00:00
-- url     : https://prove2.me/submissions/53a3a0fd-2504-4572-8b44-51718c6c1839

import Definitions.Def_SZ_Slice
import Mathlib.Tactic.Push
import Definitions.Def_SZ_SliceHygiene
import Theorems.Thm_SZ_Slice_sq_pos
import Theorems.Thm_SZ_Slice_sq_sq


set_option autoImplicit false
open SZ
open SZ.Slice
variable {S : Slice}
namespace SZ.Slice
theorem _root_.solution (he : S.e = (S.m : ℤ) - 1) (hp : (S.p : ℝ) ≤ S.sq) :
    (S.p : ℝ) * S.sq + (S.p : ℝ) ≤ (S.e : ℝ) + S.sq + 1 := by
  have hecast : (S.e : ℝ) = (S.m : ℝ) - 1 := by rw [he]; push_cast; ring
  have hsq := S.sq_sq
  have hpos := S.sq_pos
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ S.sq - (S.p : ℝ))
    (by linarith : (0:ℝ) ≤ S.sq + 1)]
end SZ.Slice
