-- Prove2me | solution 1 for TunnellMap.canonicalEta_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:29:55.223803+00:00
-- url     : https://prove2.me/submissions/184eb832-543b-4515-ab33-7a4abcd8dfa3

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
import Theorems.Thm_TunnellMap_canonicalEta_mem

set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hnpos : 0 < n)
    (q : (bResidualInvolution n).Orbit)
    (o : (aResidualInvolution n hnpos).Orbit) :
    canonicalEta hnpos q o * canonicalEta hnpos q o = 1 := by
  rcases canonicalEta_mem hnpos q o with h | h <;> rw [h] <;> ring
end TunnellMap
