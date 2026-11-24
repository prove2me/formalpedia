-- Prove2me | solution 1 for ULHC.MP.B_opt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:17:06.633488+00:00
-- url     : https://prove2.me/submissions/cfa2da7d-777d-4090-87ff-a563d44645c9

import Mathlib
import Definitions.Def_ULHC_MinPath
import Theorems.Thm_ULHC_MP_isTail_nil
import Theorems.Thm_ULHC_MP_pw_cons
import Theorems.Thm_ULHC_MP_amin_le
import Theorems.Thm_ULHC_MP_B_succ

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable [DecidableEq α]
variable (NL : List α) (src mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
namespace ULHC.MP
theorem _root_.solution : ∀ (k : ℕ) (x : α) (L : List α), IsTail mid tgt edge x L →
    (∀ z ∈ x :: L, z ∈ NL) → L.length < k →
      ∃ r, B NL mid tgt edge w k x = some r ∧ r.1 ≤ pw w (x :: L) := by
  intro k
  induction k with
  | zero =>
    intro x L _ _ hl
    exact absurd hl (Nat.not_lt_zero _)
  | succ k ih =>
    intro x L ht hN hl
    have hxN : x ∈ NL := hN x (by simp)
    rw [B_succ, if_pos hxN]
    unfold step
    by_cases htg : tgt x = true
    · rw [if_pos htg]
      refine ⟨_, rfl, ?_⟩
      show w x ≤ pw w (x :: L)
      rw [pw_cons]
      omega
    · rw [if_neg htg]
      cases L with
      | nil => exact absurd (isTail_nil.1 ht) htg
      | cons y L =>
        obtain ⟨hm, he, ht'⟩ := ht
        rw [if_pos hm]
        have hyN : ∀ z ∈ y :: L, z ∈ NL := fun z hz => hN z (List.mem_cons_of_mem x hz)
        have hl' : L.length < k := by
          rw [List.length_cons] at hl
          omega
        obtain ⟨r, hr, hr'⟩ := ih y L ht' hyN hl'
        have hf : (if edge x y then
              (B NL mid tgt edge w k y).map (fun r => (w x + r.1, x :: r.2)) else none) =
            some (w x + r.1, x :: r.2) := by
          rw [if_pos he, hr]
          rfl
        obtain ⟨r2, h2, h2'⟩ := amin_le
          (f := fun y => if edge x y then
            (B NL mid tgt edge w k y).map (fun r => (w x + r.1, x :: r.2)) else none)
          ((hyN y (by simp))) hf
        refine ⟨r2, h2, ?_⟩
        rw [pw_cons]
        exact h2'.trans (by show w x + r.1 ≤ w x + pw w (y :: L); omega)
end ULHC.MP
