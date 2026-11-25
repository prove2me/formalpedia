-- Prove2me | solution 1 for SZ.Slice.form_b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:27:17.441528+00:00
-- url     : https://prove2.me/submissions/674e99c3-1a78-4693-8c1b-fbcc125eb6f6

import Definitions.Def_SZ_Slice
import Mathlib.Tactic.Push
import Definitions.Def_SZ_SliceHygiene
import Theorems.Thm_SZ_Slice_U_eq_one_add
import Theorems.Thm_SZ_Slice_sq_pos
import Theorems.Thm_SZ_Slice_sq_sq


set_option autoImplicit false
open SZ
open SZ.Slice
variable {S : Slice}
namespace SZ.Slice
theorem _root_.solution (he : S.e = (S.m : ℤ) - 1) (hp : (S.p : ℝ) ≤ S.sq) :
    (S.p : ℝ) * S.sq ≤ (S.m : ℝ) * (S.U - (S.p : ℝ)) := by
  have hU := U_eq_one_add he
  have hsq := S.sq_sq
  have hpos := S.sq_pos
  rw [hU]
  nlinarith [mul_nonneg (mul_nonneg hpos.le (by linarith : (0:ℝ) ≤ S.sq + 1))
    (by linarith : (0:ℝ) ≤ S.sq - (S.p : ℝ))]
end SZ.Slice
