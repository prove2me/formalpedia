-- Prove2me | solution 1 for Psi.stEast_getLast_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:26:39.802793+00:00
-- url     : https://prove2.me/submissions/3cfb8ccc-c285-4301-bc5e-88db3591d58d

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p : List Bool) (hp : p.getLast? = some false) (x : Bool) :
    stEast p x = true := by
  induction p generalizing x with
  | nil => simp at hp
  | cons a t ih => cases t with
      | nil => simp at hp; subst hp; rfl
      | cons b s => rw [List.getLast?_cons_cons] at hp; cases a <;> exact ih hp _
end Psi
