-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.parEps_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:12:28.166848+00:00
-- url     : https://prove2.me/submissions/f1a4faed-df7e-445c-80d9-84e487616fe3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_LowerStepStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_AdjGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_InterlacesULt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap
open ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS.Lap
theorem _root_.solution {k r : ℕ} (a : Fin (2 * r + k + 1)) (ha : a.val + 1 < 2 * r + k + 1)
    (hne : parEps k r a ≠ parEps k r ⟨a.val + 1, ha⟩) : k - 1 ≤ a.val := by
  by_contra hlt
  have h1 : a.val < k - 1 := by omega
  have hl : parEps k r a = true := by
    show (if a.val < k - 1 then true else decide ((a.val - (k - 1)) % 2 = 0)) = true
    rw [if_pos h1]
  have hr : parEps k r ⟨a.val + 1, ha⟩ = true := by
    show (if a.val + 1 < k - 1 then true else decide ((a.val + 1 - (k - 1)) % 2 = 0)) = true
    split
    · rfl
    · rw [show a.val + 1 - (k - 1) = 0 by omega]
      rfl
  exact hne (hl.trans hr.symm)
end ReciprocityTheory.ChartRestriction.DS.Lap
