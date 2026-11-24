-- Prove2me | solution 1 for Psi.phi_numRises
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:51:43.543746+00:00
-- url     : https://prove2.me/submissions/d9fcb535-6279-48e8-91b1-979353f13243

import Definitions.Def_RequestProject_Psi_PathLemmas
import Definitions.Def_RequestProject_Psi_PhiBasic
import Theorems.Thm_Psi_phi_isDyck
import Theorems.Thm_Psi_len_filter_split
import Theorems.Thm_Psi_phi_numValleys
import Theorems.Thm_Psi_count_split
import Theorems.Thm_Psi_numN_phiPath
import Theorems.Thm_Psi_dyck_head
import Theorems.Thm_Psi_phiPath_ne_nil


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (w : List Bool) (av : List ℕ) :
    numRises (phiPath w av) = (w.filter id).length := by
  have hd := phi_isDyck w av
  have hne := phiPath_ne_nil w av
  have hh : (phiPath w av).head? = some true := dyck_head _ hd hne
  have hcs := count_split (phiPath w av) hh
  have hnv := phi_numValleys w av
  have hnn := numN_phiPath w av
  have hlen := len_filter_split w
  rw [hnv, hnn] at hcs
  omega
end Psi
