-- Prove2me | solution 1 for Psi.count_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:33:02.196275+00:00
-- url     : https://prove2.me/submissions/2d9a7294-b71d-410f-9c73-0b8bc55f2fcf

import Definitions.Def_RequestProject_Psi_PathLemmas
import Definitions.Def_RequestProject_Psi_PhiBasic
import Theorems.Thm_Psi_numN_count

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p : List Bool) (h : p.head? = some true) :
    numRises p + numValleys p + 1 = numN p := by
  have h2 := numN_count p false false
  simp only [h, and_true, if_true] at h2
  simp only [numRises, numValleys]
  omega
end Psi
