-- Prove2me | solution 1 for Psi.riseComp_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:40:45.827173+00:00
-- url     : https://prove2.me/submissions/62857069-f31d-49df-844b-f9164ea77481

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp
import Theorems.Thm_Psi_northRunsAux_replicate_true
import Theorems.Thm_Psi_northRunsAux_zero_eq
import Theorems.Thm_Psi_cc_noDD_append_gen
import Theorems.Thm_Psi_northRuns_cc_cons_false

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (rho rho' : List Bool) (hrho : hasDD rho = false) :
    northRuns (cc rho')
      = ppart ((northRuns (cc (rho ++ rho'))).headD 0 - numN rho)
        ++ (northRuns (cc (rho ++ rho'))).tail := by
  set T := (if stEast rho false then cc (false :: rho') else cc rho') with hT
  have h1 : northRuns (cc (rho ++ rho')) = northRunsAux T (numN rho) := by
    rw [northRuns, cc_noDD_append_gen rho rho' hrho, northRunsAux_replicate_true, Nat.zero_add,
      ← hT]
  have hTAIL : northRuns T = northRuns (cc rho') := by
    rw [hT]
    by_cases hs : stEast rho false = true
    · rw [if_pos hs, northRuns_cc_cons_false]
    · rw [if_neg hs]
  rw [h1, ← northRunsAux_zero_eq T (numN rho)]
  exact hTAIL.symm
end Psi
