-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.MV.inner_def
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:51:51.365822+00:00
-- url     : https://prove2.me/submissions/f027c536-cadc-4afe-ba21-3d3e062791f4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelSpace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelInner

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
namespace MV
theorem _root_.solution {ε : Fin n → Bool} {m : Fin n → ℤ} (f g : MV ε m) : inner ℂ f g = mvInner f g := rfl
end MV
end ReciprocityTheory.ChartRestriction.DS.HW
