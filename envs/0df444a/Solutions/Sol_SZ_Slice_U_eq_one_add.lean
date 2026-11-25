-- Prove2me | solution 1 for SZ.Slice.U_eq_one_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:59:05.941465+00:00
-- url     : https://prove2.me/submissions/f0bd53d2-92aa-4930-bc0d-0735617303e0

import Definitions.Def_SZ_Slice
import Mathlib.Tactic.Push
import Definitions.Def_SZ_SliceHygiene
import Theorems.Thm_SZ_Slice_M_eq_one
import Theorems.Thm_SZ_Slice_U_eq


set_option autoImplicit false
open SZ
open SZ.Slice
variable {S : Slice}
namespace SZ.Slice
theorem _root_.solution (he : S.e = (S.m : ℤ) - 1) : S.U = 1 + S.sq := by
  rw [S.U_eq, M_eq_one he, one_mul]
end SZ.Slice
