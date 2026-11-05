-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFiniteLedger.simultaneous_representation_and_ledger
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:27:12.117499+00:00
-- url     : https://prove2.me/submissions/29b76b96-99d1-4789-ada7-fef43cfcddc4

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryFiniteLedger
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalFiniteLedger_simultaneous_fixed_block
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCoverScale_fixed_representation_eventually


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFiniteLedger
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open scoped Topology
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFiniteLedger
theorem _root_.solution (c d : ℕ) :
    ∃ c' : ℕ, c ≤ c' ∧ GoodBlock (scale 40000000000 c' d) ∧
      ∀ᶠ n : ℕ in atTop,
        ((localFactor 40000000000 c' d)^
          (radixLength (scale 40000000000 c' d) n) : ℝ) ≤
            (n : ℝ)^(1/10000000000 : ℝ) := by
  obtain ⟨c',hc',hg⟩ := simultaneous_fixed_block 40000000000 c d
  exact ⟨c',hc',hg,fixed_representation_eventually c' d⟩
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFiniteLedger
