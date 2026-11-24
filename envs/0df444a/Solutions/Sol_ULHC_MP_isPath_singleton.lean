-- Prove2me | solution 1 for ULHC.MP.isPath_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:17:36.522728+00:00
-- url     : https://prove2.me/submissions/a181a2b4-af9e-4142-aabe-f9e3641fd8ae

import Mathlib
import Definitions.Def_ULHC_MinPath

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable {src mid tgt : α → Bool} {edge : α → α → Bool} {w : α → ℕ}
namespace ULHC.MP
theorem _root_.solution {x : α} :
    IsPath src mid tgt edge [x] ↔ src x = true ∧ tgt x = true := Iff.rfl
end ULHC.MP
