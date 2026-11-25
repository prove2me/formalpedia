-- Prove2me | solution 1 for SZ.Slice.stt_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:54:43.313813+00:00
-- url     : https://prove2.me/submissions/346dbb86-e97f-44f5-9774-ad5b734cd9ff

import Definitions.Def_SZ_Slice
import Mathlib.Tactic.Push
import Definitions.Def_SZ_SliceHygiene

set_option autoImplicit false
open SZ
open SZ.Slice
variable {S : Slice}
namespace SZ.Slice
theorem _root_.solution (S : Slice) (j k₀ : ℤ) (k : ℕ) :
    stt S j k₀ (k + 1) = ((S.m : ℤ) * ((stt S j k₀ k).1 - S.dA (S.w0 j k₀) k),
      (S.m : ℤ) * ((stt S j k₀ k).2 - S.dB (S.w0 j k₀) k)) := rfl
end SZ.Slice
