-- Prove2me | solution 1 for ULHC.MP.pick_le_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:12:39.35318+00:00
-- url     : https://prove2.me/submissions/32c25fe0-1f23-4271-b2c4-e60d1dbceab3

import Mathlib
import Definitions.Def_ULHC_MinPath

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable {γ β : Type}
namespace ULHC.MP
theorem _root_.solution {a b : Option (ℕ × β)} {r : ℕ × β} (h : a = some r) :
    ∃ r', pick a b = some r' ∧ r'.1 ≤ r.1 := by
  subst h
  rcases b with _ | b
  · exact ⟨r, rfl, le_refl _⟩
  · by_cases hb : b.1 < r.1
    · exact ⟨b, by simp only [pick, if_pos hb], le_of_lt hb⟩
    · exact ⟨r, by simp only [pick, if_neg hb], le_refl _⟩
end ULHC.MP
