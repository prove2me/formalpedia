-- Prove2me | solution 1 for ThreeSum.WeightedGlobalGoodOutputCatalog.cap_real_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:20:26.610001+00:00
-- url     : https://prove2.me/submissions/9cb3c6b3-47ff-46f7-b7a0-a779b0a58a4e

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryLiteralOutputCap
import Definitions.Def_Submission_Weighted_Global_TernaryCoverGoodMaps
import Definitions.Def_Submission_ThreeSum_TernaryFixedDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Mathlib.Algebra.Order.Floor.Div
import Definitions.Def_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_cap_le_iff

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
theorem _root_.solution (τ : ℕ) : (cap m p τ : ℝ)≤
    ((partitionLoss (2380004124000*m) (292746547000*m)*p*τ : ℕ) : ℝ)/(Rbar m : ℝ)+1 := by
  have hR : 0<Rbar m := by unfold Rbar; positivity
  have hRR : (0 : ℝ)<Rbar m := by exact_mod_cast hR
  by_cases hz : cap m p τ=0
  · rw [hz,Nat.cast_zero]
    positivity
  · have hpos : 0<cap m p τ := by omega
    have hlt : Rbar m*(cap m p τ-1)<partitionLoss (2380004124000*m) (292746547000*m)*p*τ := by
      by_contra hn
      have hh := (cap_le_iff (m := m) (p := p) τ (cap m p τ-1)).mpr (by omega)
      omega
    have hcast : ((cap m p τ-1 : ℕ) : ℝ)=(cap m p τ : ℝ)-1 := by
      rw [Nat.cast_sub (show 1≤cap m p τ by omega)]
      norm_num
    have hltR : (Rbar m : ℝ)*((cap m p τ : ℝ)-1)<
        ((partitionLoss (2380004124000*m) (292746547000*m)*p*τ : ℕ) : ℝ) := by
      have hh : (Rbar m : ℝ)*((cap m p τ-1 : ℕ) : ℝ)<
          ((partitionLoss (2380004124000*m) (292746547000*m)*p*τ : ℕ) : ℝ) := by exact_mod_cast hlt
      rwa [hcast] at hh
    have hh : (cap m p τ : ℝ)-1≤
        ((partitionLoss (2380004124000*m) (292746547000*m)*p*τ : ℕ) : ℝ)/(Rbar m : ℝ) :=
      (le_div_iff₀ hRR).mpr (by nlinarith [hltR])
    linarith
end ThreeSum.WeightedGlobalGoodOutputCatalog
