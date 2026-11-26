-- Prove2me | solution 1 for TunnellMap.aResidual_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:15:06.436167+00:00
-- url     : https://prove2.me/submissions/80a09d76-822d-450b-9b21-ec04fc01c08e

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
import Theorems.Thm_TunnellMap_FreeInvolution_signAct_signOf_canonicalRepresentative

set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hnpos : 0 < n) (y : AResidual n) :
    signActA hnpos (aResidualSign hnpos y)
        (canonicalAResidualRepresentative hnpos
          ((aResidualInvolution n hnpos).orbit y)) = y :=
  (aResidualInvolution n hnpos).signAct_signOf_canonicalRepresentative
    aResidualLexKey aResidualLexKey_injective y
end TunnellMap
