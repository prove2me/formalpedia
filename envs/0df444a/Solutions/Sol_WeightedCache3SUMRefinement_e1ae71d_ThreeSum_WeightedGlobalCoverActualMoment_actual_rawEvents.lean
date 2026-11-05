-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverActualMoment.actual_rawEvents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:20:35.658381+00:00
-- url     : https://prove2.me/submissions/dbdf43da-000b-40f0-9a42-c734fa29cbb1

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryCoverHighMoment
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalLocalParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverActualMoment
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCoverActualMoment_cast_taggedLeft
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCoverActualMoment_cast_taggedRight

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverActualMoment
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open TernaryCoverHighMoment TernaryCoverRankFibers WeightedGlobalLocalParameters
open TernaryCoverOutputCap
open scoped BigOperators
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverActualMoment
theorem _root_.solution {L p : ℕ} [Fact p.Prime] (α π : DigitType) (a b : ZMod p) :
    rawEvents (fun e : LocalEdge L α π => taggedLeft e) taggedRight a b =
      (fun e => pairEvent (fieldLeft (p := p) e) (fieldRight e) a b) := by
  funext e
  unfold rawEvents pairEvent linearHash
  rw [cast_taggedLeft, cast_taggedRight]
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverActualMoment
