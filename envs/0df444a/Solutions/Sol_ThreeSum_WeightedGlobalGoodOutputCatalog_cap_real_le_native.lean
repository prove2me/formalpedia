-- Prove2me | solution 1 for ThreeSum.WeightedGlobalGoodOutputCatalog.cap_real_le_native
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:31:59.202889+00:00
-- url     : https://prove2.me/submissions/6c44f010-da50-4580-9036-71721663df0d

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryLiteralOutputCap
import Definitions.Def_Submission_Weighted_Global_TernaryCoverGoodMaps
import Definitions.Def_Submission_ThreeSum_TernaryFixedDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Mathlib.Algebra.Order.Floor.Div
import Definitions.Def_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_cap_real_le_twice
import Theorems.Thm_ThreeSum_TernaryTypeLowerBound_partition_cap_le_prime
import Theorems.Thm_ThreeSum_WeightedGlobalLocalParameters_fixedPi_space
import Theorems.Thm_ThreeSum_WeightedGlobalLocalParameters_fixedPi_total


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalGoodOutputCatalog
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open WeightedGlobalCoverGoodMaps TernaryCoverFibers WeightedGlobalLocalParameters WeightedGlobalPartitionCount
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000
variable {m p : ℕ} [Fact p.Prime]
variable {I : Type*} [Fintype I] [DecidableEq I]
namespace ThreeSum.WeightedGlobalGoodOutputCatalog
theorem _root_.solution (τ : ℕ) (hτ : 0<τ)
    (hP : (vertices (fixedLength m) (fixedPi m)).card*Rbar m≤p^2) :
    (cap m p τ : ℝ)≤2*(((partitionLoss (2380004124000*m) (292746547000*m)*p*τ : ℕ) : ℝ)/(Rbar m : ℝ)) := by
  have hR : Rbar m≤p := TernaryTypeLowerBound.partition_cap_le_prime
    (fixedPi m) (fixedPi_total m) (fixedPi_space m) p hP
  have hLoss : 0<partitionLoss (2380004124000*m) (292746547000*m) := by unfold partitionLoss; positivity
  have hp1 : p≤partitionLoss (2380004124000*m) (292746547000*m)*p := Nat.le_mul_of_pos_left p hLoss
  have hp2 : partitionLoss (2380004124000*m) (292746547000*m)*p≤partitionLoss (2380004124000*m) (292746547000*m)*p*τ :=
    Nat.le_mul_of_pos_right _ hτ
  exact cap_real_le_twice τ (hR.trans (hp1.trans hp2))
end ThreeSum.WeightedGlobalGoodOutputCatalog
