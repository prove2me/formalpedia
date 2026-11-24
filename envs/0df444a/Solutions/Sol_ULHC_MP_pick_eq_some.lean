-- Prove2me | solution 1 for ULHC.MP.pick_eq_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:12:33.943814+00:00
-- url     : https://prove2.me/submissions/d738658d-b2d5-4d09-9eb0-4c5ce3fb6aba

import Mathlib
import Definitions.Def_ULHC_MinPath

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable {γ β : Type}
namespace ULHC.MP
theorem _root_.solution {a b : Option (ℕ × β)} {r : ℕ × β} (h : pick a b = some r) :
    a = some r ∨ b = some r := by
  rcases a with _ | a
  · exact Or.inr h
  · rcases b with _ | b
    · exact Or.inl h
    · simp only [pick] at h
      by_cases hb : b.1 < a.1
      · rw [if_pos hb] at h
        exact Or.inr h
      · rw [if_neg hb] at h
        exact Or.inl h
end ULHC.MP
