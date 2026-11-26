-- Prove2me | solution 1 for Supersequence.skipGap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:58:00.457359+00:00
-- url     : https://prove2.me/submissions/e2675c46-d0d4-4156-a30e-544569e88adf

import Std
import Definitions.Def_Frequency

set_option autoImplicit true
open Supersequence
open List
variable {α : Type}
namespace Supersequence
theorem _root_.solution {x : α} {v g r : List α} (hx : x ∉ g)
    (h : (x :: v).Sublist (g ++ r)) : (x :: v).Sublist r := by
  induction g with
  | nil => exact h
  | cons a g ih =>
    have hxa : x ≠ a := by intro e; exact hx (by simp [e])
    apply ih (fun hm => hx (.tail _ hm))
    rcases sublist_cons_iff.mp h with h | ⟨s,he,_⟩
    · exact h
    · simp_all
end Supersequence
