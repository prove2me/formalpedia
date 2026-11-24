-- Prove2me | solution 1 for Psi.desComp_noDescent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:34:38.24122+00:00
-- url     : https://prove2.me/submissions/2d300871-2577-467c-9da5-1c4e47e767f5

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
import Theorems.Thm_Psi_desCompAux_noDescent
import Theorems.Thm_Psi_noDescent_cons_false


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution {w : List Bool} (hnd : noDescent w = true) :
    desComp (false :: w) = [w.length + 1] := by
  have h : noDescent (false :: w) = true := by rw [noDescent_cons_false]; exact hnd
  unfold desComp
  rw [desCompAux_noDescent (false :: w) h 0]; simp
end Psi
