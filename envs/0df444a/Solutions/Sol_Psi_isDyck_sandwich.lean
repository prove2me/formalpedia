-- Prove2me | solution 1 for Psi.isDyck_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:27:34.684422+00:00
-- url     : https://prove2.me/submissions/c988fcd2-b89d-41ee-95ac-dd6b446cec38

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
import Theorems.Thm_Psi_runHeight_append
import Theorems.Thm_Psi_validFrom_append
import Theorems.Thm_Psi_isDyckAux_iff
import Theorems.Thm_Psi_runHeight_replicate_true
import Theorems.Thm_Psi_runHeight_replicate_false
import Theorems.Thm_Psi_validFrom_replicate_true
import Theorems.Thm_Psi_validFrom_replicate_false
import Theorems.Thm_Psi_runHeight_shift
import Theorems.Thm_Psi_validFrom_mono
import Theorems.Thm_Psi_runHeight_nonneg
import Theorems.Thm_Psi_runHeight_flatten_UD
import Theorems.Thm_Psi_validFrom_flatten_UD

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a b : ℕ) (rho rho' : List Bool)
    (hv : validFrom rho 0) (hv' : validFrom rho' (runHeight rho 0))
    (he : runHeight rho' (runHeight rho 0) = 0) :
    IsDyck ((List.replicate a [true, false]).flatten ++ [true] ++ rho
      ++ List.replicate b true ++ List.replicate (b + 1) false ++ rho') := by
  have hρ0 : 0 ≤ runHeight rho 0 := runHeight_nonneg rho 0 le_rfl hv
  set F := (List.replicate a [true, false]).flatten with hF
  have hA : runHeight F 0 = 0 := runHeight_flatten_UD a 0
  have hB : runHeight (F ++ [true]) 0 = 1 := by rw [runHeight_append, hA]; norm_num [runHeight]
  have hC : runHeight (F ++ [true] ++ rho) 0 = runHeight rho 0 + 1 := by
    rw [runHeight_append, hB]; simpa using runHeight_shift rho 0 1
  have hD : runHeight (F ++ [true] ++ rho ++ List.replicate b true) 0 = runHeight rho 0 + 1 + b := by
    rw [runHeight_append, hC, runHeight_replicate_true]
  have hE : runHeight (F ++ [true] ++ rho ++ List.replicate b true ++ List.replicate (b + 1) false) 0
      = runHeight rho 0 := by
    rw [runHeight_append, hD, runHeight_replicate_false]; push_cast; ring
  rw [IsDyck, isDyckAux_iff]
  refine ⟨?_, ?_⟩
  · rw [validFrom_append, validFrom_append, validFrom_append, validFrom_append, validFrom_append]
    refine ⟨⟨⟨⟨⟨validFrom_flatten_UD _ 0 le_rfl, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · rw [hA]; simp [validFrom]
    · rw [hB]; exact validFrom_mono rho 0 1 (by norm_num) hv
    · rw [hC]; exact validFrom_replicate_true _ _
    · rw [hD]; apply validFrom_replicate_false; push_cast; omega
    · rw [hE]; exact hv'
  · rw [runHeight_append, hE]; exact he
end Psi
