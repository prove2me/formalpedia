-- Prove2me | solution 1 for Psi.numN_replicate_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:55:23.798434+00:00
-- url     : https://prove2.me/submissions/c5a057ce-a051-4e49-9033-087709b47cff

import Definitions.Def_RequestProject_Psi_PathLemmas
import Definitions.Def_RequestProject_Psi_PhiBasic

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (n : Nat) : numN (List.replicate n true) = n := by
  induction n with
  | zero => simp [numN]
  | succ m ih => rw [List.replicate_succ]; unfold numN at ih ⊢; simp
end Psi
