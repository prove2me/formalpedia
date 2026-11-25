-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.rsPt_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:12:46.9459+00:00
-- url     : https://prove2.me/submissions/037f1fc5-9a87-4339-bc8e-ea0d3743c6a0

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
theorem _root_.solution (k r : ℕ) (u : Fin k → ℝ) (b : Fin (2 * r + 2) → ℝ) (t j m : ℕ)
    (hk : 1 ≤ k) (hj : 1 ≤ j) (hj2 : j ≤ 2 * r + 1) :
    rsPt k r u b t j (m + 1) =
      rsPt k r u b t j m + Pi.single (⟨j + k - 1, by omega⟩ : Fin (2 * r + k + 1)) 1 := by
  funext a
  have ha := a.isLt
  simp only [Pi.add_apply, Pi.single_apply, rsPt, rsF, rsG, rsExt, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | (exfalso; omega) | ring1 | (push_cast; ring1) | (subst_vars; push_cast; ring1) | (subst_vars; ring1)
end ReciprocityTheory.ChartRestriction.DS.Lap
