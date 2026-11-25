-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.kfa_toMK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:15:18.795477+00:00
-- url     : https://prove2.me/submissions/1b7545d3-303a-4c69-b237-a660edcc5fb7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFactsA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (t : ℝ) :
    toMK (kfaKG ε hY t) = NormedSpace.exp ((t : ℂ) • Y) := rfl
end ReciprocityTheory.ChartRestriction.DS.S7
