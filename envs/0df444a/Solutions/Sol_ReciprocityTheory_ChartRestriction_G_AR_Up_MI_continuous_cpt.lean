-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.continuous_cpt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:02:11.944624+00:00
-- url     : https://prove2.me/submissions/24bfcd57-f2da-4048-a3b0-b518e835ad8f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfL
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_continuous_NF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_cpt_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates
  ReciprocityTheory.ChartRestriction.G.AR.Up
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution (x0 : Frame X.Ψ r) : Continuous (cpt X x0) := by
  rw [show cpt X x0 = fun z => rmul x0 (NF X (ΦC X z)) from funext (cpt_eq X x0)]
  refine continuous_pi fun τ => ?_
  show Continuous fun z => mat x0 τ * mat (NF X (ΦC X z)) τ
  exact continuous_const.matrix_mul (((continuous_apply τ).comp (continuous_NF X)).comp (ΦC X).continuous)
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
