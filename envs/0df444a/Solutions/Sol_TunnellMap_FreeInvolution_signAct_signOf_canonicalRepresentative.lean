-- Prove2me | solution 1 for TunnellMap.FreeInvolution.signAct_signOf_canonicalRepresentative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:12:52.764133+00:00
-- url     : https://prove2.me/submissions/37bffdca-88b7-4afe-b83e-9409fdbb5c16

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
import Theorems.Thm_TunnellMap_FreeInvolution_signAct_signOf_canonicalPoint

set_option autoImplicit true
open TunnellMap
open TunnellMap.FreeInvolution
variable {X : Type*} (I : FreeInvolution X)
variable {K : Type*} [LinearOrder K]
namespace TunnellMap.FreeInvolution
theorem _root_.solution (key : X → K)
    (hkey : Function.Injective key) (x : X) :
    I.signAct (I.signOf key x)
      (I.canonicalRepresentative key hkey (I.orbit x)) = x := by
  rw [canonicalRepresentative_orbit]
  exact I.signAct_signOf_canonicalPoint key x
end TunnellMap.FreeInvolution
