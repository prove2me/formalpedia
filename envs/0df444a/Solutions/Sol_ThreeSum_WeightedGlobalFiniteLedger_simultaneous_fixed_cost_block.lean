-- Prove2me | solution 1 for ThreeSum.WeightedGlobalFiniteLedger.simultaneous_fixed_cost_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:15:14.72582+00:00
-- url     : https://prove2.me/submissions/348fd016-a5ef-485d-a214-5dbbc2b7b29f

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Theorems.Thm_ThreeSum_WeightedGlobalFiniteLedger_goodBlock_eventually
import Theorems.Thm_ThreeSum_WeightedGlobalFiniteLedger_positive_slopes_eventually
import Theorems.Thm_ThreeSum_WeightedGlobalFiniteLedger_scale_ge_coefficient

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalFiniteLedger
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open scoped Topology
namespace ThreeSum.WeightedGlobalFiniteLedger
theorem _root_.solution (C c d : ℕ) :
    ∃ c' : ℕ, c ≤ c' ∧ GoodBlock (scale C c' d) ∧
      0 < outputRate (scale C c' d) ∧ primeRate (scale C c' d) < outputRate (scale C c' d) := by
  have hgood : ∀ᶠ m : ℕ in atTop, GoodBlock m ∧ 0 < outputRate m ∧ primeRate m < outputRate m := by
    filter_upwards [goodBlock_eventually,positive_slopes_eventually] with m hg hp
    exact ⟨hg,hp⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp hgood
  refine ⟨max c N,le_max_left _ _,hN _ ?_⟩
  exact (le_max_right c N).trans (scale_ge_coefficient _ _ _)
end ThreeSum.WeightedGlobalFiniteLedger
