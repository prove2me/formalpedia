-- Prove2me | solution 1 for ThreeSum.TernaryCoverActualMoment.tagged_endpoint_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:55:21.426042+00:00
-- url     : https://prove2.me/submissions/b7a680bf-f6e0-4263-8046-c41187409d4a

import Definitions.Def_Submission_ThreeSum_TernaryCoverHighMoment
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
import Definitions.Def_Submission_ThreeSum_TernaryCoverActualMoment
import Theorems.Thm_ThreeSum_TernaryCoverLocal_field_endpoint_injective


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverActualMoment
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open TernaryCoverHighMoment TernaryCoverRankFibers TernaryLocalParameters
open TernaryCoverOutputCap
open scoped BigOperators
namespace ThreeSum.TernaryCoverActualMoment
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
end ThreeSum.TernaryCoverActualMoment
