-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredRuntimeCertificate.query_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T03:41:04.545791+00:00
-- url     : https://prove2.me/submissions/19460354-b3a1-47cb-803e-0668726a1162

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredTerminalReceipt
import Definitions.Def_Submission_Weighted_Global_TernaryColoredFinalReady
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPrefixRuntimeIdentity
import Definitions.Def_Submission_Weighted_Global_TernaryColoredRuntimeBounds
import Definitions.Def_Submission_Weighted_Global_TernaryColoredQueryBudget
import Definitions.Def_Submission_Weighted_Global_TernaryProfileRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryColoredRuntimeCertificate
import Theorems.Thm_ThreeSum_WeightedGlobalColoredRuntimeCertificate_query_cap
import Theorems.Thm_ThreeSumApsp_Dominated_trans
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_trans
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_KeepInputs_trans
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial
import Theorems.Thm_ThreeSum_WeightedGlobalColoredQueryBudget_query_time_bound


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredRuntimeCertificate
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalColoredLoopSetup
open WeightedGlobalColoredTerminalReceipt WeightedGlobalActualPrefixRuntime
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000
variable {κ : ℕ}
variable (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (initial : ℕ→ℤ)
variable [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]
namespace ThreeSum.WeightedGlobalColoredRuntimeCertificate
theorem _root_.solution (hmeta : WeightedGlobalPreparedOriginals.Metadata n (n^κ) A B C)
    (hn : 1<n) :
    (WeightedGlobalActualGlobalQueryRuntime.queryCap (state P n free menu c A B C initial) n:ℝ)≤
      (WeightedGlobalUniformQueryTime.coefficient P.m P.wordD P.allocation.E κ:ℝ)*
        ((state P n free menu c A B C initial).arena.J+1:ℕ)^3*
          WeightedGlobalCountFrontendBudget.envelope P.m (WeightedGlobalCoverScale.radixLength P.m n) := by
  exact (Nat.cast_le.mpr (query_cap P n free menu c A B C initial)).trans
    (WeightedGlobalColoredQueryBudget.query_time_bound P n free A B C hn hmeta.lengthA hmeta.lengthB hmeta.lengthC)
end ThreeSum.WeightedGlobalColoredRuntimeCertificate
