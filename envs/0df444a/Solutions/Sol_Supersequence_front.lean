-- Prove2me | solution 1 for Supersequence.front
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:58:44.559327+00:00
-- url     : https://prove2.me/submissions/400121b9-7a9b-4a06-b376-b639e1fb472f

import Std
import Definitions.Def_Frequency
import Theorems.Thm_Supersequence_skipGap
import Theorems.Thm_Supersequence_project_append
import Theorems.Thm_Supersequence_project_cons_self
attribute [local simp] Supersequence.project_append
attribute [local simp] Supersequence.project_cons_self

set_option autoImplicit true
open Supersequence
open List
variable {α : Type}
variable [DecidableEq α]
omit [DecidableEq α]
namespace Supersequence
theorem _root_.solution {x : α} {g r : List α} (hg : x ∉ g)
    (hw : Covers (fun _ => True) (g ++ r)) : Covers (· ≠ x) r := by
  intro q hn hq
  exact sublist_of_cons_sublist (skipGap hg (hw (x::q) (by
    simp [hn]; exact fun hm => hq x hm rfl) (by simp)))
end Supersequence
