-- Prove2me | solution 1 for Psi.noDescent_of_desc
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-23T23:47:56.244797+00:00
-- url     : https://prove2.me/submissions/6873ede6-1978-4575-a0c4-2037dde7b590

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi


theorem solution (s t : List Bool) : noDescent (s ++ true :: false :: t) = false := by
  induction s with
  | nil => simp [noDescent]
  | cons a s ih =>
    cases s with
    | nil => cases a <;> simp [noDescent]
    | cons b s => change ((!a || b) && noDescent ((b :: s) ++ true :: false :: t)) = false; rw [ih, Bool.and_false]
