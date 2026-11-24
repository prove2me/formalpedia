-- Prove2me | solution 1 for Psi.numNBeforeDD_fUD
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-23T23:46:18.488026+00:00
-- url     : https://prove2.me/submissions/66c7ec48-5b4d-4725-a76f-f1f9b96f9804

import Definitions.Def_RequestProject_Psi_Inverse
import Definitions.Def_RequestProject_Psi_Bijection
set_option autoImplicit true
open Psi


theorem solution (m : ℕ) :
    numNBeforeDD ((List.replicate m [true, false]).flatten) = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    cases m with
    | zero => rfl
    | succ k => simpa [List.replicate_succ, numNBeforeDD] using congrArg Nat.succ ih
