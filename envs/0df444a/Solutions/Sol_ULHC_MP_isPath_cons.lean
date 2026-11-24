-- Prove2me | solution 1 for ULHC.MP.isPath_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:52:55.732844+00:00
-- url     : https://prove2.me/submissions/b7d5670d-7904-4f21-944b-a8c03bcc45d4

import Mathlib
import Definitions.Def_ULHC_MinPath

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable {src mid tgt : α → Bool} {edge : α → α → Bool} {w : α → ℕ}
namespace ULHC.MP
theorem _root_.solution {x : α} {L : List α} :
    IsPath src mid tgt edge (x :: L) ↔ src x = true ∧ IsTail mid tgt edge x L := Iff.rfl
end ULHC.MP
