-- Prove2me | solution 1 for ThreeSum.LightLocalCoverSchedule.indices_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:49:48.471662+00:00
-- url     : https://prove2.me/submissions/7fe93af2-700c-4dfc-981b-2fa87a8c056f

import Definitions.Def_Submission_ThreeSum_LightLocalCoverTransport
import Definitions.Def_Submission_ThreeSum_LocalCoverMatrix
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
import Definitions.Def_Submission_ThreeSum_LightCoverGreedy
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
import Theorems.Thm_ThreeSum_BooleanGreedy_choices_length


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverSchedule
open Finset LocalHashMoments LocalCoverBounds GlobalEncoding
namespace ThreeSum.LightLocalCoverSchedule
theorem _root_.solution (h : ℕ) : (indices h).length = scheduleSize h :=
  BooleanGreedy.choices_length ..
end ThreeSum.LightLocalCoverSchedule
