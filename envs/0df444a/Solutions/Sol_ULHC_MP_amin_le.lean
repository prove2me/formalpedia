-- Prove2me | solution 1 for ULHC.MP.amin_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:14:28.252827+00:00
-- url     : https://prove2.me/submissions/dc68f0f6-3771-44ae-91ea-021c2eba70e1

import Mathlib
import Definitions.Def_ULHC_MinPath
import Theorems.Thm_ULHC_MP_pick_le_left
import Theorems.Thm_ULHC_MP_pick_le_right

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable {γ β : Type}
namespace ULHC.MP
theorem _root_.solution {f : γ → Option (ℕ × β)} {l : List γ} {y : γ} {r : ℕ × β}
    (hy : y ∈ l) (h : f y = some r) : ∃ r', amin f l = some r' ∧ r'.1 ≤ r.1 := by
  induction l with
  | nil => cases hy
  | cons z zs ih =>
    simp only [amin]
    rcases List.mem_cons.1 hy with rfl | hy'
    · exact pick_le_left h
    · obtain ⟨r1, h1, h1'⟩ := ih hy'
      obtain ⟨r2, h2, h2'⟩ := pick_le_right (a := f z) h1
      exact ⟨r2, h2, h2'.trans h1'⟩
end ULHC.MP
