-- Prove2me | solution 1 for Psi.stEast_fUD_false_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:28:21.654271+00:00
-- url     : https://prove2.me/submissions/79b1d08c-8890-4ee4-88e1-c9bf0492244c

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
import Theorems.Thm_Psi_stEast_append
import Theorems.Thm_Psi_stEast_UDpair
import Theorems.Thm_Psi_fUD_succ
import Theorems.Thm_Psi_stEast_fUD_true

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a : Nat) : stEast (fUD (a+1)) false = true := by
  rw [fUD_succ, stEast_append, stEast_UDpair, stEast_fUD_true]
end Psi
