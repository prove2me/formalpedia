-- Prove2me | solution 1 for Psi.tau_headD_le_numN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:35:49.356668+00:00
-- url     : https://prove2.me/submissions/1b71c737-598a-4123-ac14-3afba0412e93

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
import Theorems.Thm_Psi_isChain_head_le_getLast
import Theorems.Thm_Psi_numN_phiPath


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (w' : List Bool) (av' : List ℕ) (hv : IsValid w' av') :
    (tauOf w' av').headD 0 ≤ numN (phiPath w' av') := by
  obtain ⟨_, hchain, hlast⟩ := hv
  rw [numN_phiPath]
  exact isChain_head_le_getLast (tauOf w' av') hchain (w'.length + 1) hlast
end Psi
