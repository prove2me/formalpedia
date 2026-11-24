-- Prove2me | solution 1 for Psi.cLead1_block
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-23T23:46:16.642665+00:00
-- url     : https://prove2.me/submissions/5bed8278-a049-47a7-8cc0-2933b4c619c9

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi


theorem solution (b : ℕ) (w' : List Bool) :
    cLead1 (List.replicate b true ++ false :: w') = b := by
  induction b with
  | zero => rfl
  | succ b ih => simp [List.replicate_succ, cLead1, ih, Nat.add_comm]
