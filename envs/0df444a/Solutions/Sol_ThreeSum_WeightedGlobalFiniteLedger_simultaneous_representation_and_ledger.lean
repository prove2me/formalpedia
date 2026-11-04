-- Prove2me | solution 1 for ThreeSum.WeightedGlobalFiniteLedger.simultaneous_representation_and_ledger
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:25:04.636936+00:00
-- url     : https://prove2.me/submissions/21e440f9-d818-42c4-b809-e14a4849fd86

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Theorems.Thm_ThreeSum_WeightedGlobalFiniteLedger_simultaneous_fixed_block
import Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_fixed_representation_eventually


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalFiniteLedger
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open scoped Topology
namespace ThreeSum.WeightedGlobalFiniteLedger
theorem _root_.solution (c d : ℕ) :
    ∃ c' : ℕ, c ≤ c' ∧ GoodBlock (scale 40000000000 c' d) ∧
      ∀ᶠ n : ℕ in atTop,
        ((localFactor 40000000000 c' d)^
          (radixLength (scale 40000000000 c' d) n) : ℝ) ≤
            (n : ℝ)^(1/10000000000 : ℝ) := by
  obtain ⟨c',hc',hg⟩ := simultaneous_fixed_block 40000000000 c d
  exact ⟨c',hc',hg,fixed_representation_eventually c' d⟩
end ThreeSum.WeightedGlobalFiniteLedger
