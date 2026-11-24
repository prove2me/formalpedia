-- Prove2me | solution 1 for Psi.cc_noDD_append_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:37:53.619799+00:00
-- url     : https://prove2.me/submissions/1d7acfa3-61aa-4c56-88b3-254abe6bd39c

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp
import Theorems.Thm_Psi_cc_noDD_append_gen

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (rho Z : List Bool) (hrho : hasDD rho = false)
    (hZ : Z.head? = some true) :
    cc (rho ++ Z) = List.replicate (numN rho) true ++ cc Z := by
  cases Z with
  | nil => simp at hZ
  | cons z zs =>
    cases z with
    | false => simp at hZ
    | true =>
      rw [cc_noDD_append_gen rho (true :: zs) hrho]
      have hif : (if stEast rho false then cc (false :: true :: zs) else cc (true :: zs))
          = cc (true :: zs) := by split <;> rfl
      rw [hif]
end Psi
