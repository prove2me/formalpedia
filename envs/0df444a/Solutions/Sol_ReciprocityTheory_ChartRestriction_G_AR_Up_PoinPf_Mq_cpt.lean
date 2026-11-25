-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.Mq_cpt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:34:40.086099+00:00
-- url     : https://prove2.me/submissions/58424e07-fa6a-49dc-a35b-653e0d5e1f2c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_gM_rmul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
theorem _root_.solution (X : Data E r) (x0 x : Frame X.Ψ r) (w : V (nd X)) (τ : X.Ψ) :
    Mq X x0 (cpt X x w) τ =
      Mq X x0 x τ * ((mat (nmat X w) τ).map (starRingEnd ℂ)).submatrix (eS X) (eS X) := by
  unfold Mq
  rw [show cpt X x w = rmul x (nmat X w) from rfl, gM_rmul, Matrix.map_mul,
    ← Matrix.submatrix_mul_equiv _ _ _ (eS X) _]
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
