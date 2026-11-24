-- Prove2me | solution 1 for Psi.runHeight_replicate_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:56:53.380694+00:00
-- url     : https://prove2.me/submissions/0423ccd4-f107-4152-905d-9eb5329e7d6b

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (n : ℕ) (h : Int) :
    runHeight (List.replicate n false) h = h - n := by
  induction n generalizing h with
  | zero => simp [runHeight]
  | succ n ih => rw [List.replicate_succ]; simp only [runHeight, ih]; push_cast; ring
end Psi
