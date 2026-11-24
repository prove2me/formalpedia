-- Prove2me | solution 1 for ULHC.MP.minPath_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:02:43.986953+00:00
-- url     : https://prove2.me/submissions/57c25c87-204c-42c8-b562-6c1977989457

import Mathlib
import Definitions.Def_ULHC_MinPath
import Theorems.Thm_ULHC_MP_minPathL_some

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable [DecidableEq α]
variable {β : Type} [LinearOrder β] (N : Finset β) (src mid tgt : β → Bool)
  (edge : β → β → Bool) (w : β → ℕ)
namespace ULHC.MP
theorem _root_.solution {p : List β} (h : minPath N src mid tgt edge w = some p) :
    IsPath src mid tgt edge p ∧ ∀ x ∈ p, x ∈ N := by
  obtain ⟨h1, h2⟩ := minPathL_some _ _ _ _ _ _ h
  exact ⟨h1, fun x hx => by simpa using h2 x hx⟩
end ULHC.MP
