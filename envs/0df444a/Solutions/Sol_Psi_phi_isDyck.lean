-- Prove2me | solution 1 for Psi.phi_isDyck
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:29:42.709499+00:00
-- url     : https://prove2.me/submissions/78706a7a-7e4c-4c84-a016-68e4c321c4b7

import Definitions.Def_RequestProject_Psi_PathLemmas
import Definitions.Def_RequestProject_Psi_PhiBasic
import Theorems.Thm_Psi_isDyckAux_iff
import Theorems.Thm_Psi_isDyck_base
import Theorems.Thm_Psi_isDyck_sandwich
import Theorems.Thm_Psi_runHeight_append
import Theorems.Thm_Psi_splitAtRow_append
import Theorems.Thm_Psi_validFrom_append


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (w : List Bool) (av : List ℕ) :
    IsDyck (phiPath w av) := by
  fun_induction phiPath w av with
  | case1 w av hnd => exact isDyck_base _ _
  | case2 w av hnd a after0 b w' hh av' pi rho rho' hsplit ihrec =>
      have hpi : IsDyck pi := ihrec
      have happ : rho ++ rho' = pi := by
        have := splitAtRow_append pi hh; rw [hsplit] at this; simpa using this
      rw [IsDyck, isDyckAux_iff] at hpi
      obtain ⟨hval, hend⟩ := hpi
      rw [← happ, validFrom_append] at hval
      rw [← happ, runHeight_append] at hend
      obtain ⟨hvalρ, hvalρ'⟩ := hval
      exact isDyck_sandwich a b rho rho' hvalρ hvalρ' hend
end Psi
