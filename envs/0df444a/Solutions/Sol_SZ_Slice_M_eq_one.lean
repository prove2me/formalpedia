-- Prove2me | solution 1 for SZ.Slice.M_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:53:48.246733+00:00
-- url     : https://prove2.me/submissions/d48efafb-3c0d-49d8-bf07-defa3fcb220e

import Definitions.Def_SZ_Slice
import Mathlib.Tactic.Push
import Definitions.Def_SZ_SliceHygiene
import Theorems.Thm_SZ_Slice_m_sub_one_ne


set_option autoImplicit false
open SZ
open SZ.Slice
variable {S : Slice}
namespace SZ.Slice
theorem _root_.solution (he : S.e = (S.m : ℤ) - 1) : S.M = 1 := by
  have h : ((S.m : ℝ) - 1) ≠ 0 := S.m_sub_one_ne
  have hcast : (S.e : ℝ) = (S.m : ℝ) - 1 := by rw [he]; push_cast; ring
  rw [M, hcast, div_self h]
end SZ.Slice
