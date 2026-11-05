-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFiniteLedger.goodBlock_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:11:27.799479+00:00
-- url     : https://prove2.me/submissions/e2ed9a15-2f52-48ee-bfb6-1cb47850b17f

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryFiniteLedger
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalFiniteLedger_bank_charge_tendsto
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalFiniteLedger_query_charge_tendsto
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalFiniteLedger_endpoint_charge_tendsto
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalFiniteLedger_histogram_charge_tendsto
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalFiniteLedger_incidence_charge_tendsto
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_ledger_individual_bounds


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFiniteLedger
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open scoped Topology
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFiniteLedger
theorem _root_.solution : ∀ᶠ m : ℕ in atTop, GoodBlock m := by
  have h := ledger_individual_bounds
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    bank_charge_tendsto.eventually (gt_mem_nhds h.1),
    query_charge_tendsto.eventually (gt_mem_nhds h.2.1),
    endpoint_charge_tendsto.eventually (gt_mem_nhds h.2.2.1),
    histogram_charge_tendsto.eventually (gt_mem_nhds h.2.2.2.1),
    incidence_charge_tendsto.eventually (gt_mem_nhds h.2.2.2.2)] with m hm hB hQ hA hP hI
  exact ⟨hm,hB,hQ,hA,hP,hI⟩
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFiniteLedger
