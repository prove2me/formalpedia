-- Prove2me | solution 1 for Psi.psi_isValid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:58:00.281429+00:00
-- url     : https://prove2.me/submissions/9bd47491-c236-47db-a7b7-c2efc20c97f4

import Definitions.Def_RequestProject_Psi_Inverse
import Definitions.Def_RequestProject_Psi_Bijection
import Theorems.Thm_Psi_psi_valid_head

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (π : List Bool) (hd : IsDyck π) (hne : π ≠ []) :
    IsValid (psiPath π).1 (psiPath π).2 :=
  (psi_valid_head π hd hne).1
end Psi
