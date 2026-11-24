-- Prove2me | solution 1 for ULHC.MP.isTail_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:57:57.652791+00:00
-- url     : https://prove2.me/submissions/c97e1899-d1f0-4088-ae83-2a84bb9ed8c9

import Mathlib
import Definitions.Def_ULHC_MinPath

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable {src mid tgt : α → Bool} {edge : α → α → Bool} {w : α → ℕ}
namespace ULHC.MP
theorem _root_.solution {x y : α} {L : List α} :
    IsTail mid tgt edge x (y :: L) ↔
      mid x = true ∧ edge x y = true ∧ IsTail mid tgt edge y L := Iff.rfl
end ULHC.MP
