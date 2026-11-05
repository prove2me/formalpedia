-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFiniteLedger.simultaneous_fixed_cost_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:18:26.521319+00:00
-- url     : https://prove2.me/submissions/81873127-7bf2-427b-91b8-4c4a0eefbaec

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryFiniteLedger
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalFiniteLedger_goodBlock_eventually
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalFiniteLedger_positive_slopes_eventually
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalFiniteLedger_scale_ge_coefficient

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFiniteLedger
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open scoped Topology
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFiniteLedger
theorem _root_.solution (C c d : ℕ) :
    ∃ c' : ℕ, c ≤ c' ∧ GoodBlock (scale C c' d) ∧
      0 < outputRate (scale C c' d) ∧ primeRate (scale C c' d) < outputRate (scale C c' d) := by
  have hgood : ∀ᶠ m : ℕ in atTop, GoodBlock m ∧ 0 < outputRate m ∧ primeRate m < outputRate m := by
    filter_upwards [goodBlock_eventually,positive_slopes_eventually] with m hg hp
    exact ⟨hg,hp⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp hgood
  refine ⟨max c N,le_max_left _ _,hN _ ?_⟩
  exact (le_max_right c N).trans (scale_ge_coefficient _ _ _)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFiniteLedger
