-- Prove2me | solution 1 for ThreeSum.WeightedGlobalParameters.all_costs_lt_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:33:20.737229+00:00
-- url     : https://prove2.me/submissions/e7d09ae2-7331-4a80-a4d9-26240a1ca7ac

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_ledger_individual_bounds

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeSum.WeightedGlobalParameters
theorem _root_.solution : ∀ t ∈ costLedger, t < certificateExponent := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ledger_individual_bounds
  intro t ht
  simp only [costLedger, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · norm_num [certificateExponent]
end ThreeSum.WeightedGlobalParameters
