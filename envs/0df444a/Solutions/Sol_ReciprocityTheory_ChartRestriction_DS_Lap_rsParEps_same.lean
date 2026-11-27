-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.rsParEps_same
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:26:29.556474+00:00
-- url     : https://prove2.me/submissions/957554ea-61cb-44be-9590-f1739bee9ba2

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
theorem _root_.solution (k r : ℕ) (a : Fin (2 * r + k + 1)) (ha : a.val + 1 < 2 * r + k + 1)
    (hne : parEps k r a ≠ parEps k r ⟨a.val + 1, ha⟩) : k - 1 ≤ a.val := by
  by_contra hcon
  apply hne
  have e1 : parEps k r a = true := by
    show (if a.val < k - 1 then true else decide ((a.val - (k - 1)) % 2 = 0)) = true
    rw [if_pos (show a.val < k - 1 by omega)]
  have e2 : parEps k r ⟨a.val + 1, ha⟩ = true := by
    show (if a.val + 1 < k - 1 then true else decide ((a.val + 1 - (k - 1)) % 2 = 0)) = true
    split_ifs with h1
    · rfl
    · have : a.val + 1 - (k - 1) = 0 := by omega
      simp [this]
  rw [e1, e2]
end ReciprocityTheory.ChartRestriction.DS.Lap
