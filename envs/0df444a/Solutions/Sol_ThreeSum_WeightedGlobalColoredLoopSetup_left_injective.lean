-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredLoopSetup.left_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T02:36:19.373456+00:00
-- url     : https://prove2.me/submissions/060da958-2644-46e1-a7b1-bc1f4c4d92a6

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryConcreteProfile
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_Submission_Weighted_Global_TernaryPreparedOriginals
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPrepareAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectorAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Theorems.Thm_ThreeSum_WeightedGlobalSignedFeatureHash_left_injective


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredLoopSetup
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
variable {κ : ℕ}
variable (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (μ : ℕ→ℤ)
variable [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]
namespace ThreeSum.WeightedGlobalColoredLoopSetup
theorem _root_.solution (hmeta : WeightedGlobalPreparedOriginals.Metadata n (n^κ) A B C)
    (hinputs : WeightedGlobalArenaFixedParameters.InputGuards P.K P.m P.radix κ n) :
    Function.Injective (fun i : Fin B.length=>fun t : Fin (J P n+2)=>
      (WeightedGlobalArenaSelectedSigned.left (n^κ) P.radix (J P n) (fun j=>B.getD j 0) i.val t.val:ZMod P.p)) := by
  apply WeightedGlobalSignedFeatureHash.left_injective (fun i : Fin B.length=>B.getD i.val 0)
    P.radix_gt_one P.basePrime hinputs.2.2.1
    (fun i=>hmeta.boundB i.val i.isLt) hmeta.injectiveB
end ThreeSum.WeightedGlobalColoredLoopSetup
