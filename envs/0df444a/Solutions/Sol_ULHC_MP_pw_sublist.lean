-- Prove2me | solution 1 for ULHC.MP.pw_sublist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:11:25.562389+00:00
-- url     : https://prove2.me/submissions/a741bf39-26cf-4f3b-a393-294a1f720e6f

import Mathlib
import Definitions.Def_ULHC_MinPath
import Theorems.Thm_ULHC_MP_pw_cons

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable {src mid tgt : α → Bool} {edge : α → α → Bool} {w : α → ℕ}
namespace ULHC.MP
theorem _root_.solution {l₁ l₂ : List α} (h : l₁.Sublist l₂) : pw w l₁ ≤ pw w l₂ := by
  induction h with
  | slnil => exact le_refl _
  | cons a _ ih =>
    rw [pw_cons]
    omega
  | cons_cons a _ ih =>
    rw [pw_cons, pw_cons]
    omega
end ULHC.MP
