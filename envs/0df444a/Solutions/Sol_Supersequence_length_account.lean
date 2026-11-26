-- Prove2me | solution 1 for Supersequence.length_account
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:58:49.629077+00:00
-- url     : https://prove2.me/submissions/0189482d-e6a6-4c45-8296-a31aa19e98d0

import Std
import Definitions.Def_Frequency
import Theorems.Thm_Supersequence_project_append
import Theorems.Thm_Supersequence_project_cons_self
attribute [local simp] Supersequence.project_append
attribute [local simp] Supersequence.project_cons_self

set_option autoImplicit true
open Supersequence
open List
variable {α : Type}
variable [DecidableEq α]
namespace Supersequence
theorem _root_.solution (x : α) (w : List α) :
    (project x w).length + w.count x = w.length := by
  induction w with
  | nil => simp [project]
  | cons a w ih =>
    by_cases e : a = x
    · subst a; simp; omega
    · simpa [project, count_cons, e, Ne.symm e, Nat.add_right_comm] using ih
end Supersequence
