-- Prove2me | solution 1 for Supersequence.projected_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:59:06.174903+00:00
-- url     : https://prove2.me/submissions/37fb664e-9da2-4879-a999-59a210409ebd

import Std
import Definitions.Def_Frequency
import Theorems.Thm_Supersequence_project_append
import Theorems.Thm_Supersequence_project_cons_self
import Theorems.Thm_Supersequence_project_free
attribute [local simp] Supersequence.project_append
attribute [local simp] Supersequence.project_cons_self

set_option autoImplicit true
open Supersequence
open List
variable {α : Type}
variable [DecidableEq α]
namespace Supersequence
theorem _root_.solution {x : α} {w : List α} {F : Nat}
    (low : LowerOnOthers x F) (cov : Covers (· ≠ x) w) : F ≤ (project x w).length := by
  apply low _ (by simp [project])
  intro q hn hq
  have h := (cov q hn hq).filter (· != x)
  rw [show q.filter (· != x) = q from project_free (fun hm => hq x hm rfl)] at h
  exact h
end Supersequence
