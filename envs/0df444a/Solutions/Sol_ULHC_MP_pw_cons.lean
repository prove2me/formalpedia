-- Prove2me | solution 1 for ULHC.MP.pw_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:36:43.445446+00:00
-- url     : https://prove2.me/submissions/cb2a7f31-9759-4ce4-8a5c-049945b3e77c

import Mathlib
import Definitions.Def_ULHC_MinPath

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable {src mid tgt : α → Bool} {edge : α → α → Bool} {w : α → ℕ}
namespace ULHC.MP
theorem _root_.solution (x : α) (L : List α) : pw w (x :: L) = w x + pw w L := by
  simp only [pw, List.map_cons, List.sum_cons]
end ULHC.MP
