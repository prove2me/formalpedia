-- Prove2me | solution 1 for ThreeSum.LightExtensionFactorPredicate.word_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:12:27.836649+00:00
-- url     : https://prove2.me/submissions/d48f9d85-7763-4ccb-b8b6-1eb04f928954

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
    word C u v≤word C U V := by
  unfold word LightExtensionFactorCheck.word LightCoefficientDecode.word
  omega
end ThreeSum.LightExtensionFactorPredicate
