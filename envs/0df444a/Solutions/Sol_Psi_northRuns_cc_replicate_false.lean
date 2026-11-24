-- Prove2me | solution 1 for Psi.northRuns_cc_replicate_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:37:37.897737+00:00
-- url     : https://prove2.me/submissions/0a273c3c-59d3-4c17-afb4-ab969e924381

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp
import Theorems.Thm_Psi_northRuns_cc_cons_false

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (n : ℕ) (X : List Bool) :
    northRuns (cc (List.replicate n false ++ X)) = northRuns (cc X) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append, northRuns_cc_cons_false, ih]
end Psi
