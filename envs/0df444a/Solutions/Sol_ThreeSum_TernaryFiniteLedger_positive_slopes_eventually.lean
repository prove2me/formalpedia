-- Prove2me | solution 1 for ThreeSum.TernaryFiniteLedger.positive_slopes_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:37:00.374207+00:00
-- url     : https://prove2.me/submissions/f08ee254-4bca-4c32-99ee-e18da5974b59

import Definitions.Def_Submission_ThreeSum_TernaryEntropyRates
import Definitions.Def_Submission_ThreeSum_TernaryDimensionBounds
import Definitions.Def_Submission_ThreeSum_TernaryFiniteLedger
import Theorems.Thm_ThreeSum_TernaryEntropyRates_actual_output_rate
import Theorems.Thm_ThreeSum_TernaryEntropyRates_actual_prime_rate
import Theorems.Thm_ThreeSum_TernaryParameters_Hpi_pos
import Theorems.Thm_ThreeSum_TernaryParameters_analytic_admissibility


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryFiniteLedger
open Filter Real TernaryParameters TernaryEntropyRates TernaryCoverScale
open scoped Topology
namespace ThreeSum.TernaryFiniteLedger
theorem _root_.solution :
    ∀ᶠ m : ℕ in atTop, 0 < outputRate m ∧ primeRate m < outputRate m := by
  have hh := actual_output_rate.eventually (lt_mem_nhds Hpi_pos)
  have hlim : 0 < Hpi-(Hpi+partitionEntropy)/2 := by
    linarith [analytic_admissibility.2.2.1]
  have hs := (actual_output_rate.sub actual_prime_rate).eventually (lt_mem_nhds hlim)
  filter_upwards [hh,hs] with m hm hs
  exact ⟨hm,by linarith⟩
end ThreeSum.TernaryFiniteLedger
