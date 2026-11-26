-- Prove2me | solution 1 for TunnellMap.orbit_canonicalAResidualRepresentative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:04:15.096923+00:00
-- url     : https://prove2.me/submissions/9f76d062-bc1d-47e3-a08e-6d23b2160d5b

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
import Theorems.Thm_TunnellMap_FreeInvolution_orbit_canonicalRepresentative


set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hnpos : 0 < n)
    (o : (aResidualInvolution n hnpos).Orbit) :
    (aResidualInvolution n hnpos).orbit
      (canonicalAResidualRepresentative hnpos o) = o :=
  (aResidualInvolution n hnpos).orbit_canonicalRepresentative aResidualLexKey
    aResidualLexKey_injective o
end TunnellMap
