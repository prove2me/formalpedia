-- Prove2me | solution 1 for ThreeSum.TernaryFiniteLedger.simultaneous_representation_and_ledger
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:37:53.220209+00:00
-- url     : https://prove2.me/submissions/7ede9b03-6d88-4e86-bd7e-38a2d5705cd0

import Definitions.Def_Submission_ThreeSum_TernaryEntropyRates
import Definitions.Def_Submission_ThreeSum_TernaryDimensionBounds
import Definitions.Def_Submission_ThreeSum_TernaryFiniteLedger
import Theorems.Thm_ThreeSum_TernaryFiniteLedger_simultaneous_fixed_block
import Theorems.Thm_ThreeSum_TernaryCoverScale_fixed_representation_eventually


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryFiniteLedger
open Filter Real TernaryParameters TernaryEntropyRates TernaryCoverScale
open scoped Topology
namespace ThreeSum.TernaryFiniteLedger
theorem _root_.solution (c d : ℕ) :
    ∃ c' : ℕ, c ≤ c' ∧ GoodBlock (scale 40000000000 c' d) ∧
      ∀ᶠ n : ℕ in atTop,
        ((localFactor 40000000000 c' d)^
          (radixLength (scale 40000000000 c' d) n) : ℝ) ≤
            (n : ℝ)^(1/10000000000 : ℝ) := by
  obtain ⟨c',hc',hg⟩ := simultaneous_fixed_block 40000000000 c d
  exact ⟨c',hc',hg,fixed_representation_eventually c' d⟩
end ThreeSum.TernaryFiniteLedger
