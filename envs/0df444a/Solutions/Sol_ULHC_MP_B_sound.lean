-- Prove2me | solution 1 for ULHC.MP.B_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:17:01.257312+00:00
-- url     : https://prove2.me/submissions/16f9ba36-e5d9-4e28-b728-33a9768cbe04

import Mathlib
import Definitions.Def_ULHC_MinPath
import Theorems.Thm_ULHC_MP_pw_nil
import Theorems.Thm_ULHC_MP_pw_cons
import Theorems.Thm_ULHC_MP_amin_mem
import Theorems.Thm_ULHC_MP_B_zero
import Theorems.Thm_ULHC_MP_B_succ

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable [DecidableEq α]
variable (NL : List α) (src mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
namespace ULHC.MP
theorem _root_.solution : ∀ (k : ℕ) (x : α) (r : ℕ × List α), B NL mid tgt edge w k x = some r →
    r.1 = pw w r.2 ∧ ∃ L, r.2 = x :: L ∧ IsTail mid tgt edge x L ∧
      (∀ z ∈ r.2, z ∈ NL) ∧ L.length < k := by
  intro k
  induction k with
  | zero =>
    intro x r h
    rw [B_zero] at h
    cases h
  | succ k ih =>
    intro x r h
    rw [B_succ] at h
    by_cases hxN : x ∈ NL
    · rw [if_pos hxN] at h
      unfold step at h
      by_cases ht : tgt x = true
      · rw [if_pos ht] at h
        obtain rfl := Option.some.inj h
        refine ⟨?_, [], rfl, ht, ?_, by simp⟩
        · show w x = pw w [x]
          rw [pw_cons, pw_nil, Nat.add_zero]
        · intro z hz
          simp only [List.mem_singleton] at hz
          subst hz
          exact hxN
      · rw [if_neg ht] at h
        by_cases hm : mid x = true
        · rw [if_pos hm] at h
          obtain ⟨y, -, hy⟩ := amin_mem h
          by_cases he : edge x y = true
          · rw [if_pos he, Option.map_eq_some_iff] at hy
            obtain ⟨r', hr', rfl⟩ := hy
            obtain ⟨h1, L, h2, h3, h4, h5⟩ := ih y r' hr'
            refine ⟨?_, r'.2, rfl, ?_, ?_, ?_⟩
            · show w x + r'.1 = pw w (x :: r'.2)
              rw [pw_cons, h1]
            · rw [h2]
              exact ⟨hm, he, h3⟩
            · intro z hz
              change z ∈ x :: r'.2 at hz
              rcases List.mem_cons.1 hz with rfl | hz
              · exact hxN
              · exact h4 z hz
            · rw [h2, List.length_cons]
              omega
          · rw [if_neg he] at hy
            cases hy
        · rw [if_neg hm] at h
          cases h
    · rw [if_neg hxN] at h
      cases h
end ULHC.MP
