-- Prove2me | solution 1 for TunnellMap.FreeInvolution.orbit_signAct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:03:57.544928+00:00
-- url     : https://prove2.me/submissions/af44d39b-0880-4007-85f2-93bd7d16c012

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift

set_option autoImplicit true
open TunnellMap
open TunnellMap.FreeInvolution
variable {X : Type*} (I : FreeInvolution X)
namespace TunnellMap.FreeInvolution
theorem _root_.solution (σ : ℤ) (x : X) :
    I.orbit (I.signAct σ x) = I.orbit x := by
  unfold signAct
  split
  · rfl
  · exact I.orbit_neg x
end TunnellMap.FreeInvolution
