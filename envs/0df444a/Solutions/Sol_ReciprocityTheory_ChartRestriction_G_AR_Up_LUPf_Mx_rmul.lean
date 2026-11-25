-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.Mx_rmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:33:08.944854+00:00
-- url     : https://prove2.me/submissions/99d9eb19-33df-4739-8d74-f7dab2f33542

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfB
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
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r)
variable {X x0}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
theorem _root_.solution (hx0 : IsOrth X x0) (z : V (nd X)) (b : Frame X.Ψ r) (τ : X.Ψ) :
    Mx X x0 (rmul (cpt X x0 z) b) τ = mat (nmat X z) τ * mat b τ := by
  show (mat x0 τ)⁻¹ * (mat x0 τ * mat (nmat X z) τ * mat b τ) = mat (nmat X z) τ * mat b τ
  have hu : IsUnit (mat x0 τ).det := (orthogonalFrame_det_ne_zero X x0 hx0 τ).isUnit
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
