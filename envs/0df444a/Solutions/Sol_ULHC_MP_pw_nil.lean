-- Prove2me | solution 1 for ULHC.MP.pw_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:58:06.115554+00:00
-- url     : https://prove2.me/submissions/2d6cc84f-f7de-4fbb-92b3-9156ab519a13

import Mathlib
import Definitions.Def_ULHC_MinPath

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable {src mid tgt : α → Bool} {edge : α → α → Bool} {w : α → ℕ}
namespace ULHC.MP
theorem _root_.solution : pw w [] = 0 := rfl
end ULHC.MP
