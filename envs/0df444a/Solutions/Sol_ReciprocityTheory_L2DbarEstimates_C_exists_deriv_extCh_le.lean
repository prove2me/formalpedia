-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.exists_deriv_extCh_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:05:15.654157+00:00
-- url     : https://prove2.me/submissions/cc572b76-5ebe-49ff-ab94-fcee271ab679

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeakA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_extCh_contDiff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_deriv_extCh_of_lt_one
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_deriv_extCh_of_two_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖deriv extCh t‖ ≤ C := by
  have hc : Continuous (deriv extCh) := extCh_contDiff.continuous_deriv (by simp)
  have hs : HasCompactSupport (deriv extCh) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 2)) ?_
    intro t ht
    rcases lt_or_ge t 1 with h1 | h1
    · exact deriv_extCh_of_lt_one h1
    · have h2 : 2 < t := by
        by_contra h2
        exact ht ⟨h1, not_lt.1 h2⟩
      exact deriv_extCh_of_two_lt h2
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨C, (norm_nonneg _).trans (hC 0), hC⟩
end ReciprocityTheory.L2DbarEstimates.C
