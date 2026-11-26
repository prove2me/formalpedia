-- Prove2me | solution 1 for TunnellMap.FreeInvolution.signOf_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:05:20.054434+00:00
-- url     : https://prove2.me/submissions/2383fb6a-e071-4be5-a0b6-7d6568015831

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift

set_option autoImplicit true
open TunnellMap
open TunnellMap.FreeInvolution
variable {X : Type*} (I : FreeInvolution X)
variable {K : Type*} [LinearOrder K]
namespace TunnellMap.FreeInvolution
theorem _root_.solution (key : X → K) (x : X) :
    I.signOf key x = 1 ∨ I.signOf key x = -1 := by
  unfold signOf; split
  · exact Or.inl rfl
  · exact Or.inr rfl
end TunnellMap.FreeInvolution
