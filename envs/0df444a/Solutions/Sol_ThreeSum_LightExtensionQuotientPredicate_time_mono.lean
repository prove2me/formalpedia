-- Prove2me | solution 1 for ThreeSum.LightExtensionQuotientPredicate.time_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:23:23.711271+00:00
-- url     : https://prove2.me/submissions/fa633abc-4af1-4c6e-b4a7-cdbf9b85be82

import Definitions.Def_Submission_ThreeSum_LightPolynomialQuotientCheck
import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientPredicate

set_option autoImplicit false
open ThreeSum ThreeSum.LightExtensionQuotientPredicate
open Light
set_option maxHeartbeats 3000000
set_option maxRecDepth 5000
namespace ThreeSum.LightExtensionQuotientPredicate
theorem _root_.solution {d p u v U V : ℕ} (hu : u≤U) (hv : v≤V) :
    time d p u v≤time d p U V := by
  unfold time LightCoefficientDecode.time LightRadixDigit.time
  gcongr
end ThreeSum.LightExtensionQuotientPredicate
