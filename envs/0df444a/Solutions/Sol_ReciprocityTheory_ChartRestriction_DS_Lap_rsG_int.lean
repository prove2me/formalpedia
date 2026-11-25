-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.rsG_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:12:35.375799+00:00
-- url     : https://prove2.me/submissions/fd53e8c6-58b4-4e4f-b1b5-0fdd0f09b25d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_LowerStepStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_AdjGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_RsParLamMinus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap
open ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS.Lap
theorem _root_.solution (B : ℕ → ℝ) (t j m q : ℕ) : ∃ z : ℤ, rsG B t j m q = -B q + z := by
  unfold rsG
  split_ifs
  · exact ⟨0, by simp⟩
  · exact ⟨(m : ℤ) - (j : ℤ) * (t : ℤ), by push_cast; ring⟩
  · exact ⟨-((q : ℤ) * (t : ℤ)), by push_cast; ring⟩
end ReciprocityTheory.ChartRestriction.DS.Lap
