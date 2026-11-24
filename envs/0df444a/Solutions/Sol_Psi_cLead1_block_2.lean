-- Prove2me | solution 2 for Psi.cLead1_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:47:46.524182+00:00
-- url     : https://prove2.me/submissions/d9e9cd2e-f574-4124-87be-f6509c8d1fe0

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
import Theorems.Thm_P2M_Psi_cLead1_true__c593a1b3f5d3
import Theorems.Thm_P2M_Psi_cLead1_false__a671fc628ec7

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (b : ℕ) (w' : List Bool) :
    cLead1 (List.replicate b true ++ false :: w') = b := by
  induction b with
  | zero => rw [List.replicate_zero, List.nil_append, cLead1_false']
  | succ n ih => rw [List.replicate_succ]; simp only [List.cons_append]; rw [cLead1_true', ih]; omega
end Psi
