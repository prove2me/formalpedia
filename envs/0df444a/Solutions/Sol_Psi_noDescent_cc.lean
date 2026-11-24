-- Prove2me | solution 1 for Psi.noDescent_cc
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-23T23:46:15.000806+00:00
-- url     : https://prove2.me/submissions/72afb99a-c419-4607-8756-841f3b5421b9

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi


theorem solution (x y : Bool) (r : List Bool) :
    noDescent (x :: y :: r) = ((!x || y) && noDescent (y :: r)) := by
  rfl
