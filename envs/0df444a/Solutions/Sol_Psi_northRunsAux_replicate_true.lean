-- Prove2me | solution 1 for Psi.northRunsAux_replicate_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:02:32.744361+00:00
-- url     : https://prove2.me/submissions/1a544ce4-8cb1-4d74-bafa-cc0de6a41716

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (n : ℕ) (X : List Bool) (c : ℕ) :
    northRunsAux (List.replicate n true ++ X) c = northRunsAux X (c + n) := by
  induction n generalizing c with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append]
    simp only [northRunsAux]
    rw [ih (c + 1)]; congr 1; omega
end Psi
