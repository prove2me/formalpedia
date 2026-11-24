-- Prove2me | solution 1 for Psi.runHeight_replicate_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:56:49.719798+00:00
-- url     : https://prove2.me/submissions/1c036ad6-26b1-4d90-adb0-ccd7b660adf6

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (n : ℕ) (h : Int) :
    runHeight (List.replicate n true) h = h + n := by
  induction n generalizing h with
  | zero => simp [runHeight]
  | succ n ih => rw [List.replicate_succ]; simp only [runHeight, ih]; push_cast; ring
end Psi
