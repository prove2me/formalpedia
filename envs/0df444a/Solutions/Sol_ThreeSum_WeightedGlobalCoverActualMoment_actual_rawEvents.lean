-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCoverActualMoment.actual_rawEvents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:11:26.779075+00:00
-- url     : https://prove2.me/submissions/6d7bea97-4d07-416b-8613-ebd1ddbdc136

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryCoverHighMoment
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
import Definitions.Def_Submission_Weighted_Global_TernaryCoverActualMoment
import Theorems.Thm_ThreeSum_WeightedGlobalCoverActualMoment_cast_taggedLeft
import Theorems.Thm_ThreeSum_WeightedGlobalCoverActualMoment_cast_taggedRight

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCoverActualMoment
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open TernaryCoverHighMoment TernaryCoverRankFibers WeightedGlobalLocalParameters
open TernaryCoverOutputCap
open scoped BigOperators
namespace ThreeSum.WeightedGlobalCoverActualMoment
theorem _root_.solution {L p : ℕ} [Fact p.Prime] (α π : DigitType) (a b : ZMod p) :
    rawEvents (fun e : LocalEdge L α π => taggedLeft e) taggedRight a b =
      (fun e => pairEvent (fieldLeft (p := p) e) (fieldRight e) a b) := by
  funext e
  unfold rawEvents pairEvent linearHash
  rw [cast_taggedLeft, cast_taggedRight]
end ThreeSum.WeightedGlobalCoverActualMoment
