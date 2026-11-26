-- Prove2me | solution 1 for TunnellMap.orbit_canonicalBResidualRepresentative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:05:18.795743+00:00
-- url     : https://prove2.me/submissions/b512cb89-f31b-4740-8b79-01cfdadf95f6

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
import Theorems.Thm_TunnellMap_FreeInvolution_orbit_canonicalRepresentative


set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
namespace TunnellMap
theorem _root_.solution
    (q : (bResidualInvolution n).Orbit) :
    (bResidualInvolution n).orbit (canonicalBResidualRepresentative q) = q :=
  (bResidualInvolution n).orbit_canonicalRepresentative bResidualLexKey
    bResidualLexKey_injective q
end TunnellMap
