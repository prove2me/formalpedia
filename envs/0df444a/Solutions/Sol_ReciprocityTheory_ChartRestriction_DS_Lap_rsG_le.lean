-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.rsG_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:12:38.84621+00:00
-- url     : https://prove2.me/submissions/3c3473e3-c2b7-456f-a11b-b09104174cec

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
theorem _root_.solution (B : ℕ → ℝ) (t j m q : ℕ) (hm : m ≤ j * t) : rsG B t j m q ≤ -B q := by
  have hmR : (m : ℝ) ≤ (j : ℝ) * t := by exact_mod_cast hm
  have hqt : (0 : ℝ) ≤ (q : ℝ) * t := by positivity
  unfold rsG
  split_ifs <;> linarith
end ReciprocityTheory.ChartRestriction.DS.Lap
