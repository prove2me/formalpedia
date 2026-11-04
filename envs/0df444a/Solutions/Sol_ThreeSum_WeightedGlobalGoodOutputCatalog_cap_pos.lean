-- Prove2me | solution 1 for ThreeSum.WeightedGlobalGoodOutputCatalog.cap_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:10:50.085132+00:00
-- url     : https://prove2.me/submissions/285c99a1-86d2-469c-8c7d-3264969ac247

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
theorem _root_.solution {τ : ℕ} (hτ : 0<τ) : 0<cap m p τ := by
  have hh := (cap_le_iff (m := m) (p := p) τ (cap m p τ)).mp le_rfl
  have hA : 0<partitionLoss (2380004124000*m) (292746547000*m)*p*τ := by
    have hp := (Fact.out : p.Prime).pos
    unfold partitionLoss
    positivity
  by_contra hn
  have hz : cap m p τ=0 := by omega
  rw [hz,mul_zero] at hh
  omega
end ThreeSum.WeightedGlobalGoodOutputCatalog
