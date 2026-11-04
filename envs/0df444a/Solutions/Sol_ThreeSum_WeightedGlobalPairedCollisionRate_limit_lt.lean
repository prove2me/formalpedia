-- Prove2me | solution 1 for ThreeSum.WeightedGlobalPairedCollisionRate.limit_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:45:24.587567+00:00
-- url     : https://prove2.me/submissions/2e3a8161-b72a-47df-b41d-aa9535a0b6e3

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPairedFamilyMargin
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCollisionRate
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_Hpi_bounds
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_Hpi_pos
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_partitionEntropy_bounds


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPairedCollisionRate
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalOversizeRates WeightedGlobalOversizePrime
open WeightedGlobalCoverScale WeightedGlobalLocalParameters
open scoped Topology
set_option maxHeartbeats 1000000
namespace ThreeSum.WeightedGlobalPairedCollisionRate
theorem _root_.solution {K : ℕ} (hK : 0<K) :
    1-partitionEntropy/Hpi-2/(K : ℝ)<(7483/10000 : ℝ) := by
  have hratio : (2517/10000 : ℝ)<partitionEntropy/Hpi := by
    apply (lt_div_iff₀ Hpi_pos).mpr
    have := Hpi_bounds.2
    have := partitionEntropy_bounds.1
    linarith
  have hk : (0 : ℝ)<K := by exact_mod_cast hK
  have hh : 0<2/(K : ℝ) := by positivity
  linarith
end ThreeSum.WeightedGlobalPairedCollisionRate
