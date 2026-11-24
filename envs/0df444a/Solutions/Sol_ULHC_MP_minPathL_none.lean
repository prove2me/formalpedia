-- Prove2me | solution 1 for ULHC.MP.minPathL_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:02:37.944796+00:00
-- url     : https://prove2.me/submissions/56a92024-c1e7-4e70-abd6-299ec0286ec3

import Mathlib
import Definitions.Def_ULHC_MinPath
import Theorems.Thm_ULHC_MP_minPathL_eq
import Theorems.Thm_ULHC_MP_amin_srcF_le

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable [DecidableEq α]
variable (NL : List α) (src mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
namespace ULHC.MP
theorem _root_.solution (h : minPathL NL src mid tgt edge w = none)
    (q : List α) (hq : IsPath src mid tgt edge q) (hqN : ∀ x ∈ q, x ∈ NL) : False := by
  obtain ⟨r, hr, -⟩ := amin_srcF_le NL src mid tgt edge w hq hqN
  rw [minPathL_eq, hr, Option.map_some] at h
  cases h
end ULHC.MP
