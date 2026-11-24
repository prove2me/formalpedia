-- Prove2me | solution 1 for Psi.numN_fUD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:56:51.536808+00:00
-- url     : https://prove2.me/submissions/45223df8-913e-4c5b-a34e-74ef93910645

import Definitions.Def_RequestProject_Psi_PathLemmas
import Definitions.Def_RequestProject_Psi_PhiBasic
import Theorems.Thm_Psi_numN_append
import Theorems.Thm_Psi_fUD_succ


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a : Nat) : numN (fUD a) = a := by
  induction a with
  | zero => simp [fUD, numN]
  | succ a ih =>
      rw [fUD_succ, numN_append, ih, show numN [true, false] = 1 from rfl]; omega
end Psi
