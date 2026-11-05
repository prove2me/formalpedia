-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizeOverhead.native_cap_exponent_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:23:49.302442+00:00
-- url     : https://prove2.me/submissions/d1c9aa98-6356-41cd-b65d-ae2269c79e4c

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeRates
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryRadixOverhead
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeOverhead
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizeOverhead_native_crude_upper
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizeOverhead_native_source_cap_upper
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCoverScale_log2_le_of_le_pow


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizeOverhead
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters TernaryCoverLocal WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
open scoped Topology
set_option maxHeartbeats 1000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizeOverhead
theorem _root_.solution {K : ℕ} (hK : 0 < K) (m k : ℕ) :
    k*capExponent (nativePrime K m) (sourceCap m (nativePrime K m)) k ≤
      20*fixedLength m+8*k^2+26+k := by
  have hp := log2_le_of_le_pow (native_crude_upper hK m)
  have hB := log2_le_of_le_pow (native_source_cap_upper K m)
  have hb : capBudget (nativePrime K m) (sourceCap m (nativePrime K m)) k ≤
      20*fixedLength m+8*k^2+26 := by unfold capBudget; omega
  have hd := Nat.div_mul_le_self (capBudget (nativePrime K m) (sourceCap m (nativePrime K m)) k+k-1) k
  rw [Nat.mul_comm] at hd
  unfold capExponent
  rw [Nat.ceilDiv_eq_add_pred_div]
  omega
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizeOverhead
