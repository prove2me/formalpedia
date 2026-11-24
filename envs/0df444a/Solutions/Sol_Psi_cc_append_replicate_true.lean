-- Prove2me | solution 1 for Psi.cc_append_replicate_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:12:23.60132+00:00
-- url     : https://prove2.me/submissions/23e3cb7d-ca3e-478b-9f2f-41e70614c556

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (n : ℕ) (X : List Bool) :
    cc (List.replicate n true ++ X) = List.replicate n true ++ cc X := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append]
    show true :: cc (List.replicate m true ++ X) = List.replicate (m + 1) true ++ cc X
    rw [ih, List.replicate_succ, List.cons_append]
end Psi
