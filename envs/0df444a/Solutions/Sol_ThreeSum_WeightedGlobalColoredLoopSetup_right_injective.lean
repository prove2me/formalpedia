-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredLoopSetup.right_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T02:19:08.219842+00:00
-- url     : https://prove2.me/submissions/a3dd2914-1d5f-4882-bc84-be85dc5a1657

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryConcreteProfile
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_Submission_Weighted_Global_TernaryPreparedOriginals
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPrepareAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectorAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Theorems.Thm_ThreeSum_WeightedGlobalSignedFeatureHash_right_injective


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
    Function.Injective (fun i : Fin C.length=>fun t : Fin (J P n+2)=>
      (WeightedGlobalArenaSelectedSigned.right (n^κ) P.radix (J P n) (fun j=>C.getD j 0) i.val t.val:ZMod P.p)) := by
  apply WeightedGlobalSignedFeatureHash.right_injective (fun i : Fin C.length=>C.getD i.val 0)
    P.radix_gt_one P.basePrime hinputs.2.2.1
    (fun i=>hmeta.boundC i.val i.isLt) hmeta.injectiveC
end ThreeSum.WeightedGlobalColoredLoopSetup
