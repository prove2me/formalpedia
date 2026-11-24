-- Prove2me | solution 1 for Psi.northRuns_cc_cons_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:12:39.159517+00:00
-- url     : https://prove2.me/submissions/36b51e7b-a3dc-4dfc-a59d-0e02165f8c80

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (X : List Bool) :
    northRuns (cc (false :: X)) = northRuns (cc X) := by
  cases X with
  | nil => rfl
  | cons b xs =>
    cases b with
    | true => rfl
    | false =>
      show northRuns (false :: cc (false :: xs)) = northRuns (cc (false :: xs))
      simp [northRuns, northRunsAux]
end Psi
