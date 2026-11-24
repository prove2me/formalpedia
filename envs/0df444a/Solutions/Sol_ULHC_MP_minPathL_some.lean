-- Prove2me | solution 1 for ULHC.MP.minPathL_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:01:46.84539+00:00
-- url     : https://prove2.me/submissions/227712c3-9ae9-4bdb-ad40-9514fd06548f

import Mathlib
import Definitions.Def_ULHC_MinPath
import Theorems.Thm_ULHC_MP_minPathL_eq
import Theorems.Thm_ULHC_MP_amin_srcF_sound

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable [DecidableEq α]
variable (NL : List α) (src mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
namespace ULHC.MP
theorem _root_.solution {p : List α} (h : minPathL NL src mid tgt edge w = some p) :
    IsPath src mid tgt edge p ∧ ∀ x ∈ p, x ∈ NL := by
  rw [minPathL_eq, Option.map_eq_some_iff] at h
  obtain ⟨r, hr, rfl⟩ := h
  exact (amin_srcF_sound NL src mid tgt edge w hr).2
end ULHC.MP
