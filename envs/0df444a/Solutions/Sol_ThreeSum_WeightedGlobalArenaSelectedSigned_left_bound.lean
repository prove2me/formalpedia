-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaSelectedSigned.left_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:51:16.518382+00:00
-- url     : https://prove2.me/submissions/891562f0-3c8c-4526-a908-0c15acc8690c

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedTerminal
import Definitions.Def_Submission_Weighted_Global_TernarySignedFeatureHash
import Definitions.Def_Submission_Weighted_Global_TernaryArenaNativeComplete
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedSigned
import Theorems.Thm_ThreeSum_TernarySignedLayout_feature_abs
import Theorems.Thm_ThreeSum_TernarySignedModes_leftRaw_abs


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSelectedSigned
open TernarySignedReduction TernarySignedLayout WeightedGlobalNativeRequesterCoverage
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSelectedTerminal WeightedGlobalArenaBudgetExistence WeightedGlobalCoverGoodMaps
set_option maxHeartbeats 5000000
variable {p m F : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaSelectedSigned
theorem _root_.solution {U radix J : ℕ} (hb : 1<radix) (B : ℕ→ℤ) (j i : ℕ) :
    (left U radix J B j i).natAbs≤radix := by
  have hh := feature_abs (TernarySignedModes.leftRaw_abs (U := U) (J := J) hb (B j)) i
  rw [←Int.natCast_natAbs] at hh
  exact_mod_cast hh
end ThreeSum.WeightedGlobalArenaSelectedSigned
