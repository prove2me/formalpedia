-- Prove2me | solution 1 for Psi.stEast_replicate_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:57:17.459811+00:00
-- url     : https://prove2.me/submissions/be127c09-709c-4c61-b063-27487e17a2e3

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (n : Nat) (x : Bool) :
    stEast (List.replicate n true) x = if 1 ≤ n then false else x := by
  induction n generalizing x with
  | zero => simp [stEast]
  | succ m ih => rw [List.replicate_succ]; simp only [stEast]; rw [ih false]; simp
end Psi
