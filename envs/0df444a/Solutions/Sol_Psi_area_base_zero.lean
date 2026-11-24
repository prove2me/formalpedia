-- Prove2me | solution 1 for Psi.area_base_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:35:42.472063+00:00
-- url     : https://prove2.me/submissions/e891f993-c85b-4e83-a963-e714155282a3

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
import Theorems.Thm_Psi_areaH_append
import Theorems.Thm_Psi_area_eq_areaH
import Theorems.Thm_Psi_areaH_replicate_false
import Theorems.Thm_Psi_areaH_replicate_true
import Theorems.Thm_Psi_areaH_fUD0
import Theorems.Thm_Psi_isDyckAux_iff
import Theorems.Thm_Psi_isDyck_base
import Theorems.Thm_Psi_runHeight_flatten_UD


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (l k : ℕ) :
    area ((List.replicate l [true, false]).flatten ++ List.replicate (k + 1) true
      ++ List.replicate (k + 1) false) = 0 := by
  have hd : validFrom ((List.replicate l [true, false]).flatten ++ List.replicate (k + 1) true
      ++ List.replicate (k + 1) false) 0 := ((isDyckAux_iff _ 0).mp (isDyck_base l k)).1
  have hAeq : areaH ((List.replicate l [true, false]).flatten) 0 false = 0 := areaH_fUD0 l false
  have hAht : runHeight ((List.replicate l [true, false]).flatten) 0 = 0 := runHeight_flatten_UD l 0
  have key : (area ((List.replicate l [true, false]).flatten ++ List.replicate (k + 1) true
      ++ List.replicate (k + 1) false) : Int) = 0 := by
    rw [area_eq_areaH _ hd, areaH_append, areaH_append, hAeq, hAht,
      areaH_replicate_true, areaH_replicate_false]
    simp
  exact_mod_cast key
end Psi
