-- Prove2me | solution 1 for ThreeSum.LightLocalCoverSchedule.rows_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:49:46.807229+00:00
-- url     : https://prove2.me/submissions/85a66e9c-0de0-405b-acac-754f75d08d8a

import Definitions.Def_Submission_ThreeSum_LightLocalCoverTransport
import Definitions.Def_Submission_ThreeSum_LocalCoverMatrix
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
import Definitions.Def_Submission_ThreeSum_LightCoverGreedy
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_pos


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverSchedule
open Finset LocalHashMoments LocalCoverBounds GlobalEncoding
namespace ThreeSum.LightLocalCoverSchedule
theorem _root_.solution (h : ℕ) : 0 < rows h := Nat.pow_pos (localPrime_pos h)
end ThreeSum.LightLocalCoverSchedule
