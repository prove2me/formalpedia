-- Prove2me | solution 1 for Psi.takeWhile_repl_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:39:59.618203+00:00
-- url     : https://prove2.me/submissions/efc7dc61-59f0-44ee-9e0e-5ade2b75cd3f

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (m : ℕ) (X : List Bool) :
    (List.replicate m true ++ X).takeWhile id = List.replicate m true ++ X.takeWhile id := by
  induction m with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.cons_append, List.takeWhile_cons]; simp
end Psi
