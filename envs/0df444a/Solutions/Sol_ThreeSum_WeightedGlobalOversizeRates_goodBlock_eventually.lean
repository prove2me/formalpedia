-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizeRates.goodBlock_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:48:10.052535+00:00
-- url     : https://prove2.me/submissions/d123bc06-e22f-4fd3-a4ba-632bec2988a7

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeRates
import Theorems.Thm_ThreeSum_WeightedGlobalOversizeRates_bank_charge_tendsto
import Theorems.Thm_ThreeSum_WeightedGlobalOversizeRates_endpoint_charge_tendsto
import Theorems.Thm_ThreeSum_WeightedGlobalOversizeRates_query_charge_tendsto
import Theorems.Thm_ThreeSum_WeightedGlobalOversizeRates_histogram_charge_tendsto
import Theorems.Thm_ThreeSum_WeightedGlobalOversizeRates_incidence_charge_tendsto
import Theorems.Thm_ThreeSum_WeightedGlobalFiniteLedger_bank_charge_tendsto
import Theorems.Thm_ThreeSum_WeightedGlobalFiniteLedger_endpoint_charge_tendsto
import Theorems.Thm_ThreeSum_WeightedGlobalFiniteLedger_histogram_charge_tendsto
import Theorems.Thm_ThreeSum_WeightedGlobalFiniteLedger_incidence_charge_tendsto
import Theorems.Thm_ThreeSum_WeightedGlobalFiniteLedger_query_charge_tendsto
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_ledger_individual_bounds


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeRates
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime
open scoped Topology
set_option maxHeartbeats 1000000
namespace ThreeSum.WeightedGlobalOversizeRates
theorem _root_.solution {K : ℕ} (hK : 100000000000000000000 ≤ K) :
    ∀ᶠ m : ℕ in atTop, GoodBlock K m := by
  have hk : 0 < K := by omega
  have hkR : (0 : ℝ) < K := by exact_mod_cast hk
  have hkR' : (100000000000000000000 : ℝ) ≤ K := by exact_mod_cast hK
  have h8 : 8/(K : ℝ) < (1/625000000 : ℝ) := (div_lt_iff₀ hkR).mpr (by linarith)
  have h10 : 10/(K : ℝ) < (1/625000000 : ℝ) := (div_lt_iff₀ hkR).mpr (by linarith)
  obtain ⟨hB,hQ,hA,hP,hI⟩ := ledger_individual_bounds
  have he : certificateExponent+(1/625000000 : ℝ)=softCertificate := by norm_num [certificateExponent,softCertificate]
  have hb : 2*bankEntropy/Hpi+8/K<softCertificate := by linarith
  have hq : 2-partitionEntropy/Hpi+2*queryEntropy/Hpi+10/K<softCertificate := by linarith
  have ha : 2*Halpha/Hpi+8/K<softCertificate := by linarith
  have hp : 1+partitionEntropy/Hpi+10/K<softCertificate := by linarith
  have hi : 2-partitionEntropy/Hpi+10/K<softCertificate := by linarith
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    (bank_charge_tendsto hk).eventually (gt_mem_nhds hb),
    (query_charge_tendsto hk).eventually (gt_mem_nhds hq),
    (endpoint_charge_tendsto hk).eventually (gt_mem_nhds ha),
    (histogram_charge_tendsto hk).eventually (gt_mem_nhds hp),
    (incidence_charge_tendsto hk).eventually (gt_mem_nhds hi)] with m hm hB hQ hA hP hI
  exact ⟨hm,hB,hQ,hA,hP,hI⟩
end ThreeSum.WeightedGlobalOversizeRates
