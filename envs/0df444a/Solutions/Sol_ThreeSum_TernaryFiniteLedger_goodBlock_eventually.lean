-- Prove2me | solution 1 for ThreeSum.TernaryFiniteLedger.goodBlock_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:41:28.697226+00:00
-- url     : https://prove2.me/submissions/7156cc9e-675a-4195-ba12-b28557f8e27c

import Definitions.Def_Submission_ThreeSum_TernaryEntropyRates
import Definitions.Def_Submission_ThreeSum_TernaryDimensionBounds
import Definitions.Def_Submission_ThreeSum_TernaryFiniteLedger
import Theorems.Thm_ThreeSum_TernaryFiniteLedger_bank_charge_tendsto
import Theorems.Thm_ThreeSum_TernaryFiniteLedger_query_charge_tendsto
import Theorems.Thm_ThreeSum_TernaryFiniteLedger_endpoint_charge_tendsto
import Theorems.Thm_ThreeSum_TernaryFiniteLedger_histogram_charge_tendsto
import Theorems.Thm_ThreeSum_TernaryFiniteLedger_incidence_charge_tendsto
import Theorems.Thm_ThreeSum_TernaryParameters_ledger_individual_bounds


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryFiniteLedger
open Filter Real TernaryParameters TernaryEntropyRates TernaryCoverScale
open scoped Topology
namespace ThreeSum.TernaryFiniteLedger
theorem _root_.solution : ∀ᶠ m : ℕ in atTop, GoodBlock m := by
  have h := ledger_individual_bounds
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    bank_charge_tendsto.eventually (gt_mem_nhds h.1),
    query_charge_tendsto.eventually (gt_mem_nhds h.2.1),
    endpoint_charge_tendsto.eventually (gt_mem_nhds h.2.2.1),
    histogram_charge_tendsto.eventually (gt_mem_nhds h.2.2.2.1),
    incidence_charge_tendsto.eventually (gt_mem_nhds h.2.2.2.2)] with m hm hB hQ hA hP hI
  exact ⟨hm,hB,hQ,hA,hP,hI⟩
end ThreeSum.TernaryFiniteLedger
