-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.Cy_subset_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:31:41.78807+00:00
-- url     : https://prove2.me/submissions/68714187-112d-4b59-8d4e-fe00de572090

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_norm_le_of_Cy

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix MeasureTheory
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution : Cy ι r ⊆ Metric.closedBall 0 2 := fun y hy =>
  mem_closedBall_zero_iff.2 ((pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => norm_le_of_Cy hy i)
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
