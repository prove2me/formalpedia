-- Prove2me | solution 1 for ThreeSum.LightExtensionQuotientSearch.word_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:42:16.978859+00:00
-- url     : https://prove2.me/submissions/4c65943c-3ced-4629-9bfc-0a3165fb44e4

import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientPredicate
import Definitions.Def_Submission_ThreeSum_LightPairSearchProgram
import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientSearch

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightExtensionQuotientSearch
open Light
open LightExtensionQuotientPredicate
set_option maxHeartbeats 1000000
variable {lim : Limits}
attribute [local instance] ThreeSum.LightExtensionQuotientSearch._p2m_local_instance_7afa0e64b3_11
namespace ThreeSum.LightExtensionQuotientSearch
theorem _root_.solution (dim p u v q : ℕ) (hu : u≤q) (hv : v≤q) :
    LightExtensionQuotientPredicate.word dim p u v ≤ LightExtensionQuotientPredicate.word dim p q q := by
  unfold LightExtensionQuotientPredicate.word LightCoefficientDecode.word
  omega
end ThreeSum.LightExtensionQuotientSearch
