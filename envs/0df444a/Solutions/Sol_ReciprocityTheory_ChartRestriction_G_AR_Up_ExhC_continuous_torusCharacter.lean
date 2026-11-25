-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC.continuous_torusCharacter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:45:56.901226+00:00
-- url     : https://prove2.me/submissions/0cd7f11f-e01a-4e1e-a78b-a0cda2680d98

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhC_normSq_tPart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhB_cont_coord


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC
open Matrix Topology Filter
open scoped ComplexOrder Matrix
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
variable {f p q N' : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC
theorem _root_.solution : Continuous fun v : V (nD f p q + N') => Real.log (1 + ‖tPart v‖ ^ 2) := by
  simp only [normSq_tPart]
  refine Continuous.log (continuous_const.add (continuous_finsetSum _ fun j _ =>
    ((cont_coord _).norm).pow 2)) fun v => ?_
  positivity
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC
