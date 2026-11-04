-- Prove2me | solution 1 for ThreeSum.TernaryFiniteLedger.simultaneous_fixed_cost_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:37:51.987894+00:00
-- url     : https://prove2.me/submissions/bcf450c9-9d6c-4d18-a810-d79905e0599c

import Definitions.Def_Submission_ThreeSum_TernaryEntropyRates
import Definitions.Def_Submission_ThreeSum_TernaryDimensionBounds
import Definitions.Def_Submission_ThreeSum_TernaryFiniteLedger
import Theorems.Thm_ThreeSum_TernaryFiniteLedger_goodBlock_eventually
import Theorems.Thm_ThreeSum_TernaryFiniteLedger_positive_slopes_eventually
import Theorems.Thm_ThreeSum_TernaryFiniteLedger_scale_ge_coefficient

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryFiniteLedger
open Filter Real TernaryParameters TernaryEntropyRates TernaryCoverScale
open scoped Topology
namespace ThreeSum.TernaryFiniteLedger
theorem _root_.solution (C c d : ℕ) :
    ∃ c' : ℕ, c ≤ c' ∧ GoodBlock (scale C c' d) ∧
      0 < outputRate (scale C c' d) ∧ primeRate (scale C c' d) < outputRate (scale C c' d) := by
  have hgood : ∀ᶠ m : ℕ in atTop, GoodBlock m ∧ 0 < outputRate m ∧ primeRate m < outputRate m := by
    filter_upwards [goodBlock_eventually,positive_slopes_eventually] with m hg hp
    exact ⟨hg,hp⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp hgood
  refine ⟨max c N,le_max_left _ _,hN _ ?_⟩
  exact (le_max_right c N).trans (scale_ge_coefficient _ _ _)
end ThreeSum.TernaryFiniteLedger
