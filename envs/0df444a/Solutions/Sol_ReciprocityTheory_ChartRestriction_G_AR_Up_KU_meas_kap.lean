-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.KU.meas_kap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:23:44.548832+00:00
-- url     : https://prove2.me/submissions/f21ae6da-dd56-4e08-80f0-d431ff1b58a6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_meas_Yb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_meas_dpow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_cont_Mx

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU
theorem _root_.solution (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) : Measurable (kap X x0 bb) := by
  unfold kap
  exact Finset.measurable_prod _ fun τ _ =>
    (meas_dpow bb).comp (meas_Yb.comp (cont_Mx X x0 τ).measurable)
end ReciprocityTheory.ChartRestriction.G.AR.Up.KU
