-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.KU.kap_rmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:58:24.404583+00:00
-- url     : https://prove2.me/submissions/9c427f5f-39f8-407b-8d34-60da3e7582ee

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_Yb_mul_right
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_tl_bor___36e688b9c17f
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_tl_bor___568b9d8f783e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_Mx_rmul

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
theorem _root_.solution (X : Data E r) (x0 x : Frame X.Ψ r) (bb : ℝ) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    kap X x0 bb (rmul x b) = kap X x0 bb x := by
  unfold kap
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Mx_rmul, Yb_mul_right _ _ (tl_bor₁₂ X hb τ) (tl_bor₂₂ X hb τ)]
end ReciprocityTheory.ChartRestriction.G.AR.Up.KU
