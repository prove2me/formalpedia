-- Prove2me | solution 1 for ThreeSum.LightExtensionFactorPredicate.time_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:14:49.506106+00:00
-- url     : https://prove2.me/submissions/0260f534-22c6-46dd-8a18-9082bb0e14f5

import Definitions.Def_Submission_ThreeSum_LightExtensionFactorCheck
import Definitions.Def_Submission_ThreeSum_LightExtensionFactorPredicate

set_option autoImplicit false
open ThreeSum ThreeSum.LightExtensionFactorPredicate
open Light
set_option maxHeartbeats 3000000
set_option maxRecDepth 5000
attribute [local instance] ThreeSum.LightExtensionFactorPredicate._p2m_local_instance_595e8f8b6a_7
namespace ThreeSum.LightExtensionFactorPredicate
theorem _root_.solution (C : Layout) {u v U V : ℕ} (hu : u≤U) (hv : v≤V) :
    time C u v≤time C U V := by
  unfold time LightExtensionFactorCheck.time LightCoefficientDecode.time LightRadixDigit.time
  gcongr
end ThreeSum.LightExtensionFactorPredicate
