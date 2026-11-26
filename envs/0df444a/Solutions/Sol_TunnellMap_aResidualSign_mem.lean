-- Prove2me | solution 1 for TunnellMap.aResidualSign_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:10:53.890743+00:00
-- url     : https://prove2.me/submissions/53548675-e01a-440f-b394-1659bfd60843

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
import Theorems.Thm_TunnellMap_FreeInvolution_signOf_mem

set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hnpos : 0 < n) (y : AResidual n) :
    aResidualSign hnpos y = 1 ∨ aResidualSign hnpos y = -1 :=
  (aResidualInvolution n hnpos).signOf_mem _ y
end TunnellMap
