-- Prove2me | solution 1 for TunnellMap.bResidualSign_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:10:46.505593+00:00
-- url     : https://prove2.me/submissions/6c091975-6d39-4526-97fa-97bce38dc2d1

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
import Theorems.Thm_TunnellMap_FreeInvolution_signOf_mem

set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
namespace TunnellMap
theorem _root_.solution (x : BResidual n) :
    bResidualSign x = 1 ∨ bResidualSign x = -1 :=
  (bResidualInvolution n).signOf_mem _ x
end TunnellMap
