-- Prove2me | solution 1 for Psi.area_eq_areaH
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:31:56.319678+00:00
-- url     : https://prove2.me/submissions/bf5dc2d4-61a1-4967-a98f-661d3919c72c

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
import Theorems.Thm_Psi_areaAux_eq_areaH

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p : List Bool) (hv : validFrom p 0) :
    (area p : Int) = areaH p 0 false := by
  have := areaAux_eq_areaH p 0 0 false (le_refl 0) (by simpa using hv)
  simpa [area] using this
end Psi
