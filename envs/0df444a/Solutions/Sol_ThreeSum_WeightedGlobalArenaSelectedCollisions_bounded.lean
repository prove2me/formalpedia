-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaSelectedCollisions.bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:22:53.909803+00:00
-- url     : https://prove2.me/submissions/e4a622c8-1ba3-430e-95a1-2f1cdabc9a3e

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFixedParameters
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedCollisions
import Theorems.Thm_ThreeSum_WeightedGlobalPairedBudgetCollision_collision_bound
import Theorems.Thm_ThreeSum_WeightedGlobalPairedCollisionRate_collision_bound


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSelectedCollisions
open WeightedGlobalCoverScale WeightedGlobalOversizePrime WeightedGlobalPairedCollisionRate
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSelectedSigned WeightedGlobalCoverGoodMaps
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedGlobalArenaSelectedCollisions
theorem _root_.solution {K m n value : ℕ} (hm : 0<m) (hn : 1<n)
    (hp : 9<nativePrime K m) (hrate : charge K m<(7483/10000 : ℝ))
    (hbudget : (nativePrime K m)^(radixLength m n)*value≤9^(radixLength m n)*n^2) :
    (value : ℝ)≤(n : ℝ)^(7483/10000 : ℝ) := by
  exact (WeightedGlobalPairedBudgetCollision.collision_bound hm hn hp hbudget).trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn.le) hrate.le)
end ThreeSum.WeightedGlobalArenaSelectedCollisions
