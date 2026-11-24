-- Prove2me | solution 1 for Psi.cV_replicate_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:08:14.396555+00:00
-- url     : https://prove2.me/submissions/e6845f52-3035-4525-b320-1567eecb161d

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (n : Nat) (le : Bool) :
    countValleys (List.replicate n false) le = 0 := by
  induction n generalizing le with
  | zero => simp [countValleys]
  | succ m ih => rw [List.replicate_succ]; simpa [countValleys] using ih true
end Psi
