-- Prove2me | solution 1 for Supersequence.project_free
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:58:43.541816+00:00
-- url     : https://prove2.me/submissions/680c84a0-4a8a-4bec-8a0e-9e0383ad00ea

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
theorem _root_.solution {x : α} {w : List α} (h : x ∉ w) : project x w = w := by
  apply filter_eq_self.mpr
  intro a ha
  simp only [bne_iff_ne]
  exact fun e => h (e ▸ ha)
end Supersequence
