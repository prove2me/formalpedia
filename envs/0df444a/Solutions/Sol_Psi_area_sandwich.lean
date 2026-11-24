-- Prove2me | solution 1 for Psi.area_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:35:50.706131+00:00
-- url     : https://prove2.me/submissions/be2a3c07-e3a0-47ac-9900-3336ba54a166

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
import Theorems.Thm_Psi_area_eq_areaH
import Theorems.Thm_Psi_area_reconstruct
import Theorems.Thm_Psi_isDyckAux_iff
import Theorems.Thm_Psi_isDyck_sandwich
import Theorems.Thm_Psi_runHeight_append
import Theorems.Thm_Psi_validFrom_append


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a b : ℕ) (rho rho' : List Bool) (hb : 1 ≤ b)
    (hnoDD : hasDD rho = false)
    (hbd : stEast rho false = false → rho'.head? = some true)
    (hpi : IsDyck (rho ++ rho')) :
    area ((List.replicate a [true, false]).flatten ++ [true] ++ rho
      ++ List.replicate b true ++ List.replicate (b + 1) false ++ rho')
      = numN rho + area (rho ++ rho') := by
  have hpiV : validFrom (rho ++ rho') 0 := ((isDyckAux_iff _ 0).mp hpi).1
  have hpiE : runHeight (rho ++ rho') 0 = 0 := ((isDyckAux_iff _ 0).mp hpi).2
  have hvrho : validFrom rho 0 := ((validFrom_append rho rho' 0).mp hpiV).1
  have hvrho' : validFrom rho' (runHeight rho 0) := ((validFrom_append rho rho' 0).mp hpiV).2
  have he : runHeight rho' (runHeight rho 0) = 0 := by rw [← runHeight_append]; exact hpiE
  have hdyckP : validFrom ((List.replicate a [true, false]).flatten ++ [true] ++ rho
      ++ List.replicate b true ++ List.replicate (b + 1) false ++ rho') 0 :=
    ((isDyckAux_iff _ 0).mp (isDyck_sandwich a b rho rho' hvrho hvrho' he)).1
  have h1 := area_eq_areaH _ hdyckP
  have h2 := area_eq_areaH (rho ++ rho') hpiV
  have h3 := area_reconstruct a b rho rho' hb hnoDD hbd
  have key : (area ((List.replicate a [true, false]).flatten ++ [true] ++ rho
      ++ List.replicate b true ++ List.replicate (b + 1) false ++ rho') : Int)
      = (numN rho : Int) + area (rho ++ rho') := by
    rw [h1, h3, ← h2]
  exact_mod_cast key
end Psi
