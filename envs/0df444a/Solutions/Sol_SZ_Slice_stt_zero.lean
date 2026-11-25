-- Prove2me | solution 1 for SZ.Slice.stt_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:54:23.252822+00:00
-- url     : https://prove2.me/submissions/bd596b7e-0c71-4c41-a03e-18a74c740dd6

import Definitions.Def_SZ_Slice
import Mathlib.Tactic.Push
import Definitions.Def_SZ_SliceHygiene

set_option autoImplicit false
open SZ
open SZ.Slice
variable {S : Slice}
namespace SZ.Slice
theorem _root_.solution (S : Slice) (j k₀ : ℤ) :
    stt S j k₀ 0 = (-S.p * j * (S.m : ℤ), (S.p * k₀ + 1) * (S.m : ℤ)) := rfl
end SZ.Slice
