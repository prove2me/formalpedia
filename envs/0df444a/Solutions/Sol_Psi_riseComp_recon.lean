-- Prove2me | solution 1 for Psi.riseComp_recon
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:39:11.274869+00:00
-- url     : https://prove2.me/submissions/9d798458-d957-4d9a-8eba-6e53d8661aa0

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp
import Theorems.Thm_Psi_northRunsAux_replicate_true
import Theorems.Thm_Psi_cc_append_replicate_true
import Theorems.Thm_Psi_cc_fUD_cons_true
import Theorems.Thm_Psi_northRuns_cc_replicate_false
import Theorems.Thm_Psi_cc_noDD_append_true

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a b hh : ℕ) (rho rho' : List Bool) (hb : 1 ≤ b)
    (hnoDD : hasDD rho = false) (hnumN : numN rho = hh) :
    northRuns (cc ((List.replicate a [true, false]).flatten ++ [true] ++ rho
        ++ List.replicate b true ++ List.replicate (b + 1) false ++ rho'))
      = (a + 1 + b + hh) :: northRuns (cc rho') := by
  set Z := List.replicate b true ++ List.replicate (b + 1) false ++ rho' with hZdef
  have hZhead : Z.head? = some true := by
    rw [hZdef]; cases b with | zero => omega | succ m => simp [List.replicate_succ]
  have hpath : (List.replicate a [true, false]).flatten ++ [true] ++ rho
        ++ List.replicate b true ++ List.replicate (b + 1) false ++ rho'
      = fUD a ++ true :: (rho ++ Z) := by
    rw [hZdef, fUD]; simp [List.append_assoc]
  have hccZ : cc Z = List.replicate b true ++ cc (List.replicate (b + 1) false ++ rho') := by
    rw [hZdef, List.append_assoc, cc_append_replicate_true]
  have hcc2 : cc (List.replicate (b + 1) false ++ rho')
      = false :: cc (List.replicate b false ++ rho') := by
    obtain ⟨p, rfl⟩ : ∃ p, b = p + 1 := ⟨b - 1, by omega⟩
    rfl
  rw [hpath, cc_fUD_cons_true, cc_noDD_append_true rho Z hnoDD hZhead, hnumN, hccZ, hcc2,
    northRuns, northRunsAux_replicate_true, northRunsAux_replicate_true,
    northRunsAux_replicate_true]
  simp only [northRunsAux]
  rw [if_pos (by omega), List.singleton_append,
    show 0 + (a + 1) + hh + b = a + 1 + b + hh from by omega]
  congr 1
  rw [← northRuns, northRuns_cc_replicate_false]
end Psi
