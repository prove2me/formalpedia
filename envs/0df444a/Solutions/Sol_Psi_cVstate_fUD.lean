-- Prove2me | solution 1 for Psi.cVstate_fUD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:30:08.275148+00:00
-- url     : https://prove2.me/submissions/7d82a89a-64d5-4828-a20b-a7cd6ecc2297

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
import Theorems.Thm_Psi_countValleys_append
import Theorems.Thm_Psi_stEast_UDpair
import Theorems.Thm_Psi_cV_UDpair_false
import Theorems.Thm_Psi_fUD_succ
import Theorems.Thm_Psi_cV_fUD_true
import Theorems.Thm_Psi_stEast_fUD_false_pos

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a : Nat) :
    countValleys (fUD a) false + (if stEast (fUD a) false then 1 else 0) = a := by
  cases a with
  | zero => simp [fUD, countValleys, stEast]
  | succ a =>
      rw [fUD_succ, countValleys_append, cV_UDpair_false, stEast_UDpair, cV_fUD_true,
        ← fUD_succ, stEast_fUD_false_pos]; simp
end Psi
