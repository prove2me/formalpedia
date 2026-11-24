-- Prove2me | solution 1 for ULHC.MP.look_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:13:30.396171+00:00
-- url     : https://prove2.me/submissions/dd5a27b2-bf71-4efe-a0f4-86c94cc9a10e

import Mathlib
import Definitions.Def_ULHC_MinPath

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable [DecidableEq α]
namespace ULHC.MP
theorem _root_.solution {β : Type} (x : α) (f : α → Option β) (l : List α) :
    look x (l.map (fun a => (a, f a))) = if x ∈ l then f x else none := by
  induction l with
  | nil => simp [look]
  | cons a tf ih =>
    simp only [List.map_cons, look]
    by_cases h : a = x
    · subst h
      simp
    · rw [if_neg h, ih]
      by_cases hx : x ∈ tf
      · rw [if_pos hx, if_pos (List.mem_cons_of_mem a hx)]
      · rw [if_neg hx, if_neg (by simp [hx, Ne.symm h])]
end ULHC.MP
