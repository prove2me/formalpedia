-- Prove2me | solution 1 for ThreeSum.LightExtensionQuotientSearch.time_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:16:11.246838+00:00
-- url     : https://prove2.me/submissions/41acd638-da10-476e-81bf-41aa0cce4ea6

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
    LightExtensionQuotientPredicate.time dim p u v ≤ LightExtensionQuotientPredicate.time dim p q q := by
  unfold LightExtensionQuotientPredicate.time LightCoefficientDecode.time LightRadixDigit.time
  have h0 := Nat.mul_le_mul_left dim hu
  have h1 := Nat.mul_le_mul_left (2*dim) hv
  nlinarith
end ThreeSum.LightExtensionQuotientSearch
