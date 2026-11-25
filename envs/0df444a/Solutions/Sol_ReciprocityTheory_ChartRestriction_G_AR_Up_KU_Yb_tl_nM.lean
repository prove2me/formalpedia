-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.KU.Yb_tl_nM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:01:25.348841+00:00
-- url     : https://prove2.me/submissions/7eea9ade-ba03-46f0-b4e2-c9384ca5aa3a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfA
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_tl_nM___dc987f14ebf4
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_tl_nM___a653c742e8e4

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU
theorem _root_.solution (X : Data E r) (z : V (nd X)) (τ : X.Ψ) : Yb (tl X (ExF.nM X z τ)) = (ExF.Zt X z τ)ᵀ := by
  rw [ExF.Zt, Matrix.transpose_transpose, Yb, tl_nM₁₂, tl_nM₂₂]
end ReciprocityTheory.ChartRestriction.G.AR.Up.KU
