-- Prove2me | solution 1 for Psi.stEast_fUD_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:26:30.13015+00:00
-- url     : https://prove2.me/submissions/034e256b-c76f-415d-839a-a68c64391071

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
import Theorems.Thm_Psi_stEast_append
import Theorems.Thm_Psi_stEast_UDpair
import Theorems.Thm_Psi_fUD_succ

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a : Nat) : stEast (fUD a) true = true := by
  induction a with
  | zero => simp [fUD, stEast]
  | succ a ih => rw [fUD_succ, stEast_append, stEast_UDpair, ih]
end Psi
