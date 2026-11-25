-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.continuous_lminor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:31:36.582604+00:00
-- url     : https://prove2.me/submissions/9936be6e-6ed7-42b4-97f5-27cd032bb431

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution (τ : ι) (i : Fin (r + 1)) : Continuous fun v : Ix ι r → ℂ => lminor (Mt v τ) i := by
  unfold Mt lminor
  refine Continuous.matrix_det ?_
  refine continuous_pi fun a => continuous_pi fun b => ?_
  exact continuous_apply _
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
