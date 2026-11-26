-- Prove2me | solution 1 for TunnellMap.Examples41.directionKey_two_vsmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:25:00.849168+00:00
-- url     : https://prove2.me/submissions/9465b643-83af-474a-8fde-0670c9846632

import Definitions.Def_TunnellMap_Examples41
import Definitions.Def_TunnellMap_Examples41Residual
import Theorems.Thm_TunnellMap_directionKey_eq_iff
import Theorems.Thm_TunnellMap_primitiveDirection_two_vsmul
attribute [local simp] TunnellMap.primitiveDirection_two_vsmul



set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000
namespace TunnellMap.Examples41
theorem _root_.solution (d : Triple) (hd : d ≠ ⟨0, 0, 0⟩) :
    directionKey (vsmul 2 d) = directionKey d := by
  rw [directionKey_eq_iff, primitiveDirection_two_vsmul hd]
end TunnellMap.Examples41
