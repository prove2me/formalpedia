-- Prove2me | solution 1 for ULHC.MP.shortcut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:12:53.430997+00:00
-- url     : https://prove2.me/submissions/27a323a4-260a-4e90-8829-a6caf9fc2275

import Mathlib
import Definitions.Def_ULHC_MinPath
import Theorems.Thm_ULHC_MP_isTail_suffix

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable {src mid tgt : α → Bool} {edge : α → α → Bool} {w : α → ℕ}
namespace ULHC.MP
theorem _root_.solution {x : α} {L : List α} (h : IsTail mid tgt edge x L) :
    ∃ L', IsTail mid tgt edge x L' ∧ (x :: L').Nodup ∧ (x :: L').Sublist (x :: L) := by
  induction L generalizing x with
  | nil => exact ⟨[], h, List.nodup_singleton x, List.Sublist.refl _⟩
  | cons y L ih =>
    obtain ⟨hm, he, ht⟩ := h
    obtain ⟨L₁, ht₁, hnd, hsub⟩ := ih ht
    by_cases hx : x ∈ y :: L₁
    · obtain ⟨A, R, hAR⟩ := List.append_of_mem hx
      have hs : (x :: R).Sublist (y :: L₁) := by
        rw [hAR]
        exact List.sublist_append_right A (x :: R)
      refine ⟨R, isTail_suffix ht₁ hAR, hnd.sublist hs, ?_⟩
      exact ((List.sublist_cons_self x R).trans (hs.trans hsub)).cons_cons x
    · exact ⟨y :: L₁, ⟨hm, he, ht₁⟩, List.nodup_cons.2 ⟨hx, hnd⟩, hsub.cons_cons x⟩
end ULHC.MP
