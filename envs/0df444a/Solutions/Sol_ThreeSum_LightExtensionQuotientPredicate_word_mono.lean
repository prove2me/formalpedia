-- Prove2me | solution 1 for ThreeSum.LightExtensionQuotientPredicate.word_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:19:01.210136+00:00
-- url     : https://prove2.me/submissions/758e2ef8-8352-4f0c-b5ec-0e8f55cd4767

import Definitions.Def_Submission_ThreeSum_LightPolynomialQuotientCheck
import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientPredicate

set_option autoImplicit false
open ThreeSum ThreeSum.LightExtensionQuotientPredicate
open Light
set_option maxHeartbeats 3000000
set_option maxRecDepth 5000
namespace ThreeSum.LightExtensionQuotientPredicate
theorem _root_.solution {d p u v U V : ℕ} (hu : u≤U) (hv : v≤V) :
    word d p u v≤word d p U V := by
  unfold word LightCoefficientDecode.word
  omega
end ThreeSum.LightExtensionQuotientPredicate
