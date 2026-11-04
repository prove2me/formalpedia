-- Prove2me | solution 1 for ThreeSum.TernaryFiniteLedger.simultaneous_fixed_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:49:03.80925+00:00
-- url     : https://prove2.me/submissions/df8345b5-abcd-4956-9b34-84c55a015d15

import Definitions.Def_Submission_ThreeSum_TernaryEntropyRates
import Definitions.Def_Submission_ThreeSum_TernaryDimensionBounds
import Definitions.Def_Submission_ThreeSum_TernaryFiniteLedger
import Theorems.Thm_ThreeSum_TernaryFiniteLedger_goodBlock_eventually
import Theorems.Thm_ThreeSum_TernaryFiniteLedger_scale_ge_coefficient

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryFiniteLedger
open Filter Real TernaryParameters TernaryEntropyRates TernaryCoverScale
open scoped Topology
namespace ThreeSum.TernaryFiniteLedger
theorem _root_.solution (C c d : ℕ) :
    ∃ c' : ℕ, c ≤ c' ∧ GoodBlock (scale C c' d) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp goodBlock_eventually
  refine ⟨max c N,le_max_left _ _,hN _ ?_⟩
  exact (le_max_right c N).trans (scale_ge_coefficient _ _ _)
end ThreeSum.TernaryFiniteLedger
