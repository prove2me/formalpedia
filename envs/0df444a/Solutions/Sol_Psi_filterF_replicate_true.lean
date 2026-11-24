-- Prove2me | solution 1 for Psi.filterF_replicate_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:28:18.370896+00:00
-- url     : https://prove2.me/submissions/e54c0f29-a35d-444c-8b96-f727500c031b

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (n : Nat) :
    ((List.replicate n true).filter (· = false)).length = 0 := by
  induction n with
  | zero => simp
  | succ m ih => rw [List.replicate_succ, List.filter_cons]; simp
end Psi
