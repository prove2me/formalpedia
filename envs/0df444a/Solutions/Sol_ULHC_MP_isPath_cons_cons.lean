-- Prove2me | solution 1 for ULHC.MP.isPath_cons_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:44:34.374002+00:00
-- url     : https://prove2.me/submissions/f8ef97d8-81c5-4354-a7ab-0e842b0b281f

import Mathlib
import Definitions.Def_ULHC_MinPath

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable {src mid tgt : α → Bool} {edge : α → α → Bool} {w : α → ℕ}
namespace ULHC.MP
theorem _root_.solution {x y : α} {L : List α} :
    IsPath src mid tgt edge (x :: y :: L) ↔
      src x = true ∧ mid x = true ∧ edge x y = true ∧ IsTail mid tgt edge y L := Iff.rfl
end ULHC.MP
