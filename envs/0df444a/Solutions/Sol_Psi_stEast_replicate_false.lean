-- Prove2me | solution 1 for Psi.stEast_replicate_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:08:14.969711+00:00
-- url     : https://prove2.me/submissions/2781c4f2-bff8-4d2e-a8f7-ad6cfd175697

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (n : Nat) (x : Bool) :
    stEast (List.replicate n false) x = if 1 ≤ n then true else x := by
  induction n generalizing x with
  | zero => simp [stEast]
  | succ m ih => rw [List.replicate_succ]; simp only [stEast]; rw [ih true]; simp
end Psi
