-- Prove2me | solution 1 for Psi.cV_fUD_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:27:46.773516+00:00
-- url     : https://prove2.me/submissions/0db1f8cf-eb17-42c0-9ab2-4986cbe5672b

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
import Theorems.Thm_Psi_countValleys_append
import Theorems.Thm_Psi_stEast_UDpair
import Theorems.Thm_Psi_cV_UDpair_true
import Theorems.Thm_Psi_fUD_succ

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a : Nat) : countValleys (fUD a) true = a := by
  induction a with
  | zero => simp [fUD, countValleys]
  | succ a ih => rw [fUD_succ, countValleys_append, cV_UDpair_true, stEast_UDpair, ih]; omega
end Psi
