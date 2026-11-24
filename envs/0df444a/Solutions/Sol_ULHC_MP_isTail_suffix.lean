-- Prove2me | solution 1 for ULHC.MP.isTail_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:11:45.109108+00:00
-- url     : https://prove2.me/submissions/bf73a3a6-32e1-4113-9ab9-86072303394c

import Mathlib
import Definitions.Def_ULHC_MinPath

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable {src mid tgt : α → Bool} {edge : α → α → Bool} {w : α → ℕ}
namespace ULHC.MP
theorem _root_.solution {x y : α} {L A R : List α} (h : IsTail mid tgt edge y L)
    (he : y :: L = A ++ x :: R) : IsTail mid tgt edge x R := by
  induction A generalizing y L with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact h
  | cons a A ih =>
    simp only [List.cons_append, List.cons.injEq] at he
    obtain ⟨rfl, hL⟩ := he
    cases L with
    | nil => simp at hL
    | cons z L => exact ih h.2.2 hL
end ULHC.MP
