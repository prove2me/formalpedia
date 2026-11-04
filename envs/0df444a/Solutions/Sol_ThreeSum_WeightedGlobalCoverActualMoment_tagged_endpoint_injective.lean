-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCoverActualMoment.tagged_endpoint_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:06:09.15721+00:00
-- url     : https://prove2.me/submissions/46f6fd95-5903-4c10-afad-c440b6549113

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryCoverHighMoment
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
import Definitions.Def_Submission_Weighted_Global_TernaryCoverActualMoment
import Theorems.Thm_ThreeSum_TernaryCoverLocal_field_endpoint_injective


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCoverActualMoment
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open TernaryCoverHighMoment TernaryCoverRankFibers WeightedGlobalLocalParameters
open TernaryCoverOutputCap
open scoped BigOperators
namespace ThreeSum.WeightedGlobalCoverActualMoment
theorem _root_.solution {L p : ℕ} [Fact p.Prime] (α π : DigitType) (hp : 2 < p) :
    Function.Injective (fun e : LocalEdge L α π =>
      (castWord (K := ZMod p) (taggedLeft e), castWord (K := ZMod p) (taggedRight e))) := by
  intro e f he
  apply field_endpoint_injective α π hp
  have hl := congrArg Prod.fst he
  have hr := congrArg Prod.snd he
  apply Prod.ext
  · funext i
    exact congrFun hl (.inl i)
  · funext i
    exact congrFun hr (.inl i)
end ThreeSum.WeightedGlobalCoverActualMoment
