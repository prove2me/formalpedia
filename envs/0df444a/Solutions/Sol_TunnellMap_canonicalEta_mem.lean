-- Prove2me | solution 1 for TunnellMap.canonicalEta_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:11:19.345599+00:00
-- url     : https://prove2.me/submissions/baa49022-1e52-4cdb-b125-8d7599b406e7

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
import Theorems.Thm_TunnellMap_etaPoint_mem

set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hnpos : 0 < n)
    (q : (bResidualInvolution n).Orbit)
    (o : (aResidualInvolution n hnpos).Orbit) :
    canonicalEta hnpos q o = 1 ∨ canonicalEta hnpos q o = -1 :=
  etaPoint_mem _ _
end TunnellMap
