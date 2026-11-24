-- Prove2me | solution 1 for Psi.takeWhile_repl_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:40:35.077609+00:00
-- url     : https://prove2.me/submissions/39ce9c38-e901-46a2-85ac-8ada9ad73345

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (m : ℕ) (X : List Bool) :
    (List.replicate m false ++ X).takeWhile (· = false)
      = List.replicate m false ++ X.takeWhile (· = false) := by
  induction m with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.cons_append, List.takeWhile_cons]; simp
end Psi
