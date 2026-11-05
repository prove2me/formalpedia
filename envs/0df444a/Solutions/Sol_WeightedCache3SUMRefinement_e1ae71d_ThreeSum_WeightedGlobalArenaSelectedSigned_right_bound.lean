-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectedSigned.right_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:05:38.210706+00:00
-- url     : https://prove2.me/submissions/6b36c0d5-3255-4215-9c45-8d28d7bc3c2c

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSelectedTerminal
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedFeatureHash
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaNativeComplete
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSelectedSigned
import Theorems.Thm_ThreeSum_TernarySignedLayout_feature_abs
import Theorems.Thm_ThreeSum_TernarySignedModes_rightRaw_abs


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectedSigned
open TernarySignedReduction TernarySignedLayout WeightedGlobalNativeRequesterCoverage
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSelectedTerminal WeightedGlobalArenaBudgetExistence WeightedGlobalCoverGoodMaps
set_option maxHeartbeats 5000000
variable {p m F : ℕ} [Fact p.Prime]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectedSigned
theorem _root_.solution {U radix J : ℕ} (hb : 1<radix) (C : ℕ→ℤ) (j i : ℕ) :
    (right U radix J C j i).natAbs≤radix := by
  have hh := feature_abs (TernarySignedModes.rightRaw_abs (U := U) (J := J) hb (C j)) i
  rw [←Int.natCast_natAbs] at hh
  exact_mod_cast hh
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectedSigned
