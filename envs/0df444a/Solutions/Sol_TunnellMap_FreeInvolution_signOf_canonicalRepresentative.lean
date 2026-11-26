-- Prove2me | solution 1 for TunnellMap.FreeInvolution.signOf_canonicalRepresentative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:01:58.576455+00:00
-- url     : https://prove2.me/submissions/c75c55cf-dbe4-4f10-a03a-83d90d0cc8ca

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
import Theorems.Thm_TunnellMap_FreeInvolution_signOf_canonicalPoint

set_option autoImplicit true
open TunnellMap
open TunnellMap.FreeInvolution
variable {X : Type*} (I : FreeInvolution X)
variable {K : Type*} [LinearOrder K]
namespace TunnellMap.FreeInvolution
theorem _root_.solution (key : X → K)
    (hkey : Function.Injective key) (q : I.Orbit) :
    I.signOf key (I.canonicalRepresentative key hkey q) = 1 := by
  induction q using Quotient.inductionOn with
  | _ x => exact I.signOf_canonicalPoint key hkey x
end TunnellMap.FreeInvolution
