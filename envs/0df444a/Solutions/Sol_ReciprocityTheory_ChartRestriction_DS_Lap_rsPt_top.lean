-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.rsPt_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:12:49.900166+00:00
-- url     : https://prove2.me/submissions/739d71f9-255d-456b-80ea-2c3b9472da4d

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
theorem _root_.solution (k r : ℕ) (u : Fin k → ℝ) (b : Fin (2 * r + 2) → ℝ) (t j : ℕ) :
    rsPt k r u b t j (j * t) = raisePar k r u b t (j + 1) := by
  funext a
  have ha := a.isLt
  simp only [rsPt, rsF, rsG, raisePar, rsExt]
  split_ifs <;> first | (exfalso; omega) | ring1 | (push_cast; ring1) | (subst_vars; push_cast; ring1) | (subst_vars; ring1)
end ReciprocityTheory.ChartRestriction.DS.Lap
