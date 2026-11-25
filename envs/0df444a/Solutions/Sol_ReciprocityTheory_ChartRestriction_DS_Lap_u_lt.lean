-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.u_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:19:10.317438+00:00
-- url     : https://prove2.me/submissions/cafc84f5-b063-43b0-8d64-b39e254739bf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_LowerStepStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_AdjGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_InterlacesULt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_interlaces_u_lt

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
theorem _root_.solution {k r : ℕ} {u : Fin k → ℝ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ}
    (hI : Interlaces k r u v b) (j l : Fin k) (hjl : j.val < l.val) : u l < u j := by
  obtain ⟨j, hj⟩ := j
  obtain ⟨l, hl⟩ := l
  have hjl' : j < l := hjl
  obtain ⟨d, rfl⟩ : ∃ d, l = j + d + 1 := ⟨l - j - 1, by omega⟩
  exact interlaces_u_lt hI j d hl
end ReciprocityTheory.ChartRestriction.DS.Lap
