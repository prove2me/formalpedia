-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.KU.meas_dpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:31:07.640293+00:00
-- url     : https://prove2.me/submissions/cbdd6f3c-b1f4-40be-8462-e4cc92c03bbc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.KU
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder
noncomputable section
attribute [local instance] ReciprocityTheory.ChartRestriction.G.AR.Up.KU.instMSMat
attribute [local instance] ReciprocityTheory.ChartRestriction.G.AR.Up.KU.instBorelMat
attribute [local instance] ReciprocityTheory.ChartRestriction.G.AR.Up.KU.instSCMat
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU
theorem _root_.solution {p q : ℕ} (s : ℝ) : Measurable fun Z : Matrix (Fin p) (Fin q) ℂ => dpow Z s := by
  unfold dpow
  exact (Complex.continuous_re.comp ((continuous_const.sub
    (continuous_id.matrix_mul continuous_id.matrix_conjTranspose)).matrix_det)).measurable.pow_const s
end ReciprocityTheory.ChartRestriction.G.AR.Up.KU
