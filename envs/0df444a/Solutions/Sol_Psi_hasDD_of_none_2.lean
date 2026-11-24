-- Prove2me | solution 2 for Psi.hasDD_of_none
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-23T23:46:17.618798+00:00
-- url     : https://prove2.me/submissions/23efd647-0399-460c-ac40-0c783c694b85

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi


theorem solution (l : List Bool) (hn : firstDDidx l = none) : hasDD l = false := by
  fun_induction firstDDidx l <;> simp_all [firstDDidx, hasDD]
