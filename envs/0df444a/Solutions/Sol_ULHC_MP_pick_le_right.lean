-- Prove2me | solution 1 for ULHC.MP.pick_le_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:13:05.211821+00:00
-- url     : https://prove2.me/submissions/5fdcf7f9-a7ad-4ff4-a9a5-537ef483a8c0

import Mathlib
import Definitions.Def_ULHC_MinPath

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable {γ β : Type}
namespace ULHC.MP
theorem _root_.solution {a b : Option (ℕ × β)} {r : ℕ × β} (h : b = some r) :
    ∃ r', pick a b = some r' ∧ r'.1 ≤ r.1 := by
  subst h
  rcases a with _ | a
  · exact ⟨r, rfl, le_refl _⟩
  · by_cases hb : r.1 < a.1
    · exact ⟨r, by simp only [pick, if_pos hb], le_refl _⟩
    · exact ⟨a, by simp only [pick, if_neg hb], not_lt.1 hb⟩
end ULHC.MP
