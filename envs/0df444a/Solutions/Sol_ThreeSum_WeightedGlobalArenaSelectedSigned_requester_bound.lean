-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaSelectedSigned.requester_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:53:42.804005+00:00
-- url     : https://prove2.me/submissions/96a71269-a23a-459b-83f0-d31eb5abfd3b

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedTerminal
import Definitions.Def_Submission_Weighted_Global_TernarySignedFeatureHash
import Definitions.Def_Submission_Weighted_Global_TernaryArenaNativeComplete
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedSigned
import Theorems.Thm_ThreeSum_TernarySignedLayout_feature_abs
import Theorems.Thm_ThreeSum_TernarySignedModes_requesterRaw_abs


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSelectedSigned
open TernarySignedReduction TernarySignedLayout WeightedGlobalNativeRequesterCoverage
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSelectedTerminal WeightedGlobalArenaBudgetExistence WeightedGlobalCoverGoodMaps
set_option maxHeartbeats 5000000
variable {p m F : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaSelectedSigned
theorem _root_.solution {U radix J : ℕ} (hb : 1<radix) (X : ℕ→ℤ) (j i : ℕ) :
    (requester U radix J X j i).natAbs≤radix := by
  have hh := feature_abs (TernarySignedModes.requesterRaw_abs (U := U) (J := J) hb
    (X (position J j)) (TernaryCarryCode.carryFromCode J (j%(2^J)))) i
  rw [←Int.natCast_natAbs] at hh
  exact_mod_cast hh
end ThreeSum.WeightedGlobalArenaSelectedSigned
