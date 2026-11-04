-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredRuntimeCertificate.query_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T03:28:37.445553+00:00
-- url     : https://prove2.me/submissions/c2f23da8-070d-4f6d-a593-893213f757f9

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredTerminalReceipt
import Definitions.Def_Submission_Weighted_Global_TernaryColoredFinalReady
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPrefixRuntimeIdentity
import Definitions.Def_Submission_Weighted_Global_TernaryColoredRuntimeBounds
import Definitions.Def_Submission_Weighted_Global_TernaryColoredQueryBudget
import Definitions.Def_Submission_Weighted_Global_TernaryProfileRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryColoredRuntimeCertificate
import Theorems.Thm_ThreeSum_WeightedGlobalActualGlobalQueryRuntime_queryCap_le
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial


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
theorem _root_.solution : WeightedGlobalActualGlobalQueryRuntime.queryCap (state P n free menu c A B C initial) n≤
    queryTime P n free A B C := by
  exact WeightedGlobalActualGlobalQueryRuntime.queryCap_le _ (fun _ _=>le_rfl) le_rfl
end ThreeSum.WeightedGlobalColoredRuntimeCertificate
