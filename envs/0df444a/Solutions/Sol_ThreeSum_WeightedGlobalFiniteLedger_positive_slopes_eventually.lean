-- Prove2me | solution 1 for ThreeSum.WeightedGlobalFiniteLedger.positive_slopes_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:53:55.636194+00:00
-- url     : https://prove2.me/submissions/d37022db-c036-4c47-9c4a-0bafc2c9b91f

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_actual_output_rate
import Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_actual_prime_rate
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_Hpi_pos
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_analytic_admissibility


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalFiniteLedger
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open scoped Topology
namespace ThreeSum.WeightedGlobalFiniteLedger
theorem _root_.solution :
    ∀ᶠ m : ℕ in atTop, 0 < outputRate m ∧ primeRate m < outputRate m := by
  have hh := actual_output_rate.eventually (lt_mem_nhds Hpi_pos)
  have hlim : 0 < Hpi-(Hpi+partitionEntropy)/2 := by
    linarith [analytic_admissibility.2.2.1]
  have hs := (actual_output_rate.sub actual_prime_rate).eventually (lt_mem_nhds hlim)
  filter_upwards [hh,hs] with m hm hs
  exact ⟨hm,by linarith⟩
end ThreeSum.WeightedGlobalFiniteLedger
