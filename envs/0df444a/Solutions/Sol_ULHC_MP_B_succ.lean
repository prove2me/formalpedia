-- Prove2me | solution 1 for ULHC.MP.B_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:14:57.768287+00:00
-- url     : https://prove2.me/submissions/fbed156c-38e0-4a0b-a4df-518be426c945

import Mathlib
import Definitions.Def_ULHC_MinPath
import Theorems.Thm_ULHC_MP_look_map

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable [DecidableEq α]
variable (NL : List α) (src mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
namespace ULHC.MP
theorem _root_.solution (k : ℕ) (x : α) :
    B NL mid tgt edge w (k + 1) x =
      if x ∈ NL then step NL mid tgt edge w (B NL mid tgt edge w k) x else none := by
  unfold B
  rw [layer, next, look_map]
end ULHC.MP
