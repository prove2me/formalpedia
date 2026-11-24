-- Prove2me | solution 1 for Psi.phiPath_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:51:14.983806+00:00
-- url     : https://prove2.me/submissions/4d703a30-a0ff-4139-aba0-6c98ee2d634a

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
import Theorems.Thm_Psi_noDescent_block
import Theorems.Thm_Psi_cLead0_block
import Theorems.Thm_Psi_cLead1_block
import Theorems.Thm_Psi_drop_block
import Theorems.Thm_Psi_drop_a_block

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a b : ℕ) (w' : List Bool) (h : ℕ) (av' : List ℕ) (hb : 1 ≤ b) :
    phiPath (List.replicate a false ++ List.replicate b true ++ [false] ++ w') (h :: av')
      = (List.replicate a [true, false]).flatten ++ [true]
          ++ (splitAtRow (phiPath w' av') h).1 ++ List.replicate b true
          ++ List.replicate (b + 1) false ++ (splitAtRow (phiPath w' av') h).2 := by
  have hword : List.replicate a false ++ List.replicate b true ++ [false] ++ w'
      = List.replicate a false ++ List.replicate b true ++ false :: w' := by simp [List.append_assoc]
  rw [hword, phiPath.eq_1, if_neg (by rw [noDescent_block a b w' hb]; simp)]
  simp only [cLead0_block a b w' hb, drop_a_block a b w', cLead1_block b w', drop_block b w',
    List.headD_cons, List.tail_cons]
end Psi
