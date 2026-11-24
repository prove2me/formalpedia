-- Prove2me | solution 1 for ULHC.MP.amin_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:14:27.391845+00:00
-- url     : https://prove2.me/submissions/cf0589bf-8a84-42a6-a641-862ec847e31c

import Mathlib
import Definitions.Def_ULHC_MinPath
import Theorems.Thm_ULHC_MP_pick_eq_some

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable {γ β : Type}
namespace ULHC.MP
theorem _root_.solution {f : γ → Option (ℕ × β)} {l : List γ} {r : ℕ × β}
    (h : amin f l = some r) : ∃ y ∈ l, f y = some r := by
  induction l with
  | nil => cases h
  | cons y ys ih =>
    simp only [amin] at h
    rcases pick_eq_some h with h1 | h1
    · exact ⟨y, by simp, h1⟩
    · obtain ⟨z, hz, hz'⟩ := ih h1
      exact ⟨z, List.mem_cons_of_mem y hz, hz'⟩
end ULHC.MP
