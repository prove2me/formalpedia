-- Prove2me | solution 1 for ThreeSum.TernaryCoverActualMoment.actual_rawEvents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:00:21.92957+00:00
-- url     : https://prove2.me/submissions/f77687ae-e513-4c7b-ad1c-2e5a860a16b5

import Definitions.Def_Submission_ThreeSum_TernaryCoverHighMoment
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
import Definitions.Def_Submission_ThreeSum_TernaryCoverActualMoment
import Theorems.Thm_ThreeSum_TernaryCoverActualMoment_cast_taggedLeft
import Theorems.Thm_ThreeSum_TernaryCoverActualMoment_cast_taggedRight

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverActualMoment
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open TernaryCoverHighMoment TernaryCoverRankFibers TernaryLocalParameters
open TernaryCoverOutputCap
open scoped BigOperators
namespace ThreeSum.TernaryCoverActualMoment
theorem _root_.solution {L p : ℕ} [Fact p.Prime] (α π : DigitType) (a b : ZMod p) :
    rawEvents (fun e : LocalEdge L α π => taggedLeft e) taggedRight a b =
      (fun e => pairEvent (fieldLeft (p := p) e) (fieldRight e) a b) := by
  funext e
  unfold rawEvents pairEvent linearHash
  rw [cast_taggedLeft, cast_taggedRight]
end ThreeSum.TernaryCoverActualMoment
