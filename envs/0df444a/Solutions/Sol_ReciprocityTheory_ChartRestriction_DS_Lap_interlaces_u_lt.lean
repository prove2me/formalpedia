-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.interlaces_u_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:12:59.831708+00:00
-- url     : https://prove2.me/submissions/6907e271-3122-4af7-b22d-c35b3b1e6004

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
theorem _root_.solution {k r : ℕ} {u : Fin k → ℝ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ}
    (hI : Interlaces k r u v b) :
    ∀ (j d : ℕ) (h1 : j + d + 1 < k), u ⟨j + d + 1, h1⟩ < u ⟨j, by omega⟩ := by
  intro j d
  induction d with
  | zero =>
    intro h1
    have hj : j < k - 1 := by omega
    have h2 := hI.1 ⟨j, hj⟩
    exact lt_trans h2.2 h2.1
  | succ d ih =>
    intro h1
    have hj : j + d + 1 < k - 1 := by omega
    have h2 := hI.1 ⟨j + d + 1, hj⟩
    have h3 := ih (by omega)
    exact lt_trans (lt_trans h2.2 h2.1) h3
end ReciprocityTheory.ChartRestriction.DS.Lap
