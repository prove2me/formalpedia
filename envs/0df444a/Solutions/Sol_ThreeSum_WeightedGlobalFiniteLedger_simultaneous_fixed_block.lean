-- Prove2me | solution 1 for ThreeSum.WeightedGlobalFiniteLedger.simultaneous_fixed_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:15:10.834832+00:00
-- url     : https://prove2.me/submissions/0112ff4c-59d3-424e-a752-7cbf4f06fec7

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Theorems.Thm_ThreeSum_WeightedGlobalFiniteLedger_goodBlock_eventually
import Theorems.Thm_ThreeSum_WeightedGlobalFiniteLedger_scale_ge_coefficient

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalFiniteLedger
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open scoped Topology
namespace ThreeSum.WeightedGlobalFiniteLedger
theorem _root_.solution (C c d : ℕ) :
    ∃ c' : ℕ, c ≤ c' ∧ GoodBlock (scale C c' d) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp goodBlock_eventually
  refine ⟨max c N,le_max_left _ _,hN _ ?_⟩
  exact (le_max_right c N).trans (scale_ge_coefficient _ _ _)
end ThreeSum.WeightedGlobalFiniteLedger
