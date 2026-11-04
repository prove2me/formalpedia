-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaSelectedSigned.right_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:51:35.240828+00:00
-- url     : https://prove2.me/submissions/4d81514e-9a79-4653-9abe-9c6cf615ee6b

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedTerminal
import Definitions.Def_Submission_Weighted_Global_TernarySignedFeatureHash
import Definitions.Def_Submission_Weighted_Global_TernaryArenaNativeComplete
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedSigned
import Theorems.Thm_ThreeSum_TernarySignedLayout_feature_abs
import Theorems.Thm_ThreeSum_TernarySignedModes_rightRaw_abs


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSelectedSigned
open TernarySignedReduction TernarySignedLayout WeightedGlobalNativeRequesterCoverage
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSelectedTerminal WeightedGlobalArenaBudgetExistence WeightedGlobalCoverGoodMaps
set_option maxHeartbeats 5000000
variable {p m F : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaSelectedSigned
theorem _root_.solution {U radix J : ℕ} (hb : 1<radix) (C : ℕ→ℤ) (j i : ℕ) :
    (right U radix J C j i).natAbs≤radix := by
  have hh := feature_abs (TernarySignedModes.rightRaw_abs (U := U) (J := J) hb (C j)) i
  rw [←Int.natCast_natAbs] at hh
  exact_mod_cast hh
end ThreeSum.WeightedGlobalArenaSelectedSigned
