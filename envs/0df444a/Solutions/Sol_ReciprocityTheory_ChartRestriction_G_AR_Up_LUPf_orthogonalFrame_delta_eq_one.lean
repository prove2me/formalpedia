-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.orthogonalFrame_delta_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:49:18.200221+00:00
-- url     : https://prove2.me/submissions/c2c44b5a-a571-4990-8e79-cbd53870e2e3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_lminor_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_orthogonalFrame_det_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
  Metric Polynomial
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {x0 : Frame X.Ψ r}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
theorem _root_.solution (hx0 : IsOrth X x0) : DeltaF X x0 x0 = 1 := by
  unfold DeltaF
  refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun k _ => ?_
  have h : Mx X x0 x0 τ = 1 := by
    unfold Mx
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (orthogonalFrame_det_ne_zero (X := X) (x0 := x0) hx0 τ))
  rw [h, lminor_one]
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
