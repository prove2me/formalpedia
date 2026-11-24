-- Prove2me | solution 1 for ULHC.MP.minPathL_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:02:35.895192+00:00
-- url     : https://prove2.me/submissions/e6891f82-8b84-45f9-939a-4dcdf89af6a2

import Mathlib
import Definitions.Def_ULHC_MinPath
import Theorems.Thm_ULHC_MP_minPathL_eq
import Theorems.Thm_ULHC_MP_amin_srcF_sound
import Theorems.Thm_ULHC_MP_amin_srcF_le

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable [DecidableEq α]
variable (NL : List α) (src mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
namespace ULHC.MP
theorem _root_.solution {p : List α} (h : minPathL NL src mid tgt edge w = some p)
    (q : List α) (hq : IsPath src mid tgt edge q) (hqN : ∀ x ∈ q, x ∈ NL) :
    pw w p ≤ pw w q := by
  obtain ⟨r, hr, hr'⟩ := amin_srcF_le NL src mid tgt edge w hq hqN
  rw [minPathL_eq, hr, Option.map_some] at h
  obtain rfl := Option.some.inj h
  rw [← (amin_srcF_sound NL src mid tgt edge w hr).1]
  exact hr'
end ULHC.MP
