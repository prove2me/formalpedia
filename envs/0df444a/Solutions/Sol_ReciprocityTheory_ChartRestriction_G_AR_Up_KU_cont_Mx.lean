-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.KU.cont_Mx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:47:54.410571+00:00
-- url     : https://prove2.me/submissions/f42bd5e9-4206-4260-9ed0-a7cad470a1e3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_cont_mat

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
theorem _root_.solution (X : Data E r) (x0 : Frame X.Ψ r) (τ : X.Ψ) : Continuous fun x => Mx X x0 x τ := by
  unfold Mx tl
  exact (continuous_const.matrix_mul (cont_mat X τ)).matrix_submatrix _ _
end ReciprocityTheory.ChartRestriction.G.AR.Up.KU
