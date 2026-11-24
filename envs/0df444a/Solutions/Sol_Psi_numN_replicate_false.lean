-- Prove2me | solution 1 for Psi.numN_replicate_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:29:02.425357+00:00
-- url     : https://prove2.me/submissions/c266a9b4-6082-4dc1-b9c9-9c55e6ea6e09

import Definitions.Def_RequestProject_Psi_PathLemmas
import Definitions.Def_RequestProject_Psi_PhiBasic

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (n : Nat) : numN (List.replicate n false) = 0 := by
  induction n with
  | zero => simp [numN]
  | succ m ih => rw [List.replicate_succ]; unfold numN at ih ⊢; simp
end Psi
