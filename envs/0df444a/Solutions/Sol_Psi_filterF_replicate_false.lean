-- Prove2me | solution 1 for Psi.filterF_replicate_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:27:40.354222+00:00
-- url     : https://prove2.me/submissions/a8c5dc84-9d15-4826-b60b-08b72dbc87b8

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (n : Nat) :
    ((List.replicate n false).filter (· = false)).length = n := by
  induction n with
  | zero => simp
  | succ m ih => rw [List.replicate_succ, List.filter_cons]; simp
end Psi
