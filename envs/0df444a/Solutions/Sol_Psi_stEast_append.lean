-- Prove2me | solution 1 for Psi.stEast_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:54:40.86518+00:00
-- url     : https://prove2.me/submissions/1905c5a0-91b5-4554-a92a-6ac531256b42

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p q : List Bool) (x : Bool) :
    stEast (p ++ q) x = stEast q (stEast p x) := by
  induction p generalizing x with
  | nil => simp [stEast]
  | cons a t ih => cases a <;> simp [stEast, ih]
end Psi
