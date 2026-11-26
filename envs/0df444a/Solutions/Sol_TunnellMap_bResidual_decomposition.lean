-- Prove2me | solution 1 for TunnellMap.bResidual_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:14:55.249828+00:00
-- url     : https://prove2.me/submissions/06e50bf9-eaa8-40be-8083-82207ba63949

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
import Theorems.Thm_TunnellMap_FreeInvolution_signAct_signOf_canonicalRepresentative

set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
namespace TunnellMap
theorem _root_.solution (x : BResidual n) :
    signActB (bResidualSign x)
        (canonicalBResidualRepresentative ((bResidualInvolution n).orbit x)) = x :=
  (bResidualInvolution n).signAct_signOf_canonicalRepresentative bResidualLexKey
    bResidualLexKey_injective x
end TunnellMap
