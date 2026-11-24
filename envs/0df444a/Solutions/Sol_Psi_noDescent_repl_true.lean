-- Prove2me | solution 1 for Psi.noDescent_repl_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:25:42.856643+00:00
-- url     : https://prove2.me/submissions/c60c5237-7ea9-4689-921c-4409b1cf2403

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (b : ℕ) : noDescent (List.replicate b true) = true := by
  induction b with
  | zero => simp [noDescent]
  | succ b ih =>
      rw [List.replicate_succ]
      cases b with
      | zero => simp [noDescent]
      | succ c => rw [List.replicate_succ] at ih ⊢; simp only [noDescent] at ih ⊢; simp_all
end Psi
