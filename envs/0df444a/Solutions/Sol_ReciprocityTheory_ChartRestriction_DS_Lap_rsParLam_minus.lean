-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.rsParLam_minus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:12:44.256281+00:00
-- url     : https://prove2.me/submissions/a15e26b0-7c2e-4e91-af32-a93dde9da442

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
theorem _root_.solution (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ)
    (a : Fin (2 * r + k + 1)) (ha : k - 1 ≤ a.val) :
    parLam k r v b a = -rsExt b (a.val - (k - 1)) := by
  have h1 : ¬ a.val < k - 1 := by omega
  have h2 : a.val - (k - 1) < 2 * r + 2 := by have := a.isLt; omega
  simp only [parLam, rsExt, dif_neg h1, dif_pos h2]
end ReciprocityTheory.ChartRestriction.DS.Lap
