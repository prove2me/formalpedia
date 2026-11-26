-- Prove2me | solution 1 for Supersequence.project_cons_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:58:18.678649+00:00
-- url     : https://prove2.me/submissions/4c486e2a-9cab-4d9e-9607-5a0d9cd08b40

import Std
import Definitions.Def_Frequency
import Theorems.Thm_Supersequence_project_append
attribute [local simp] Supersequence.project_append

set_option autoImplicit true
open Supersequence
open List
variable {α : Type}
variable [DecidableEq α]
namespace Supersequence
theorem _root_.solution (x : α) (w : List α) :
    project x (x :: w) = project x w := by simp [project]
end Supersequence
