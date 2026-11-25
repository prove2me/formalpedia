-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.split_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:03:39.860389+00:00
-- url     : https://prove2.me/submissions/4b6c3a95-8301-42be-86d9-3d444c36484f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_Lm_lowU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_orthogonalFrame_det_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_nmat_zF

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
theorem _root_.solution (hx0 : IsOrth X x0) (x : Frame X.Ψ r) :
    x = rmul (cpt X x0 (zF X x0 x)) (bF X x0 x) := by
  funext τ
  have hu0 : IsUnit (mat x0 τ).det := (orthogonalFrame_det_ne_zero X x0 hx0 τ).isUnit
  have hL : IsUnit (Lm (Mx X x0 x τ)).det := by rw [(Lm_lowU _).det]; exact isUnit_one
  show mat x τ = (mat x0 τ * mat (nmat X (zF X x0 x)) τ) * mat (bF X x0 x) τ
  rw [nmat_zF]
  show mat x τ = (mat x0 τ * (Lm (Mx X x0 x τ))⁻¹) * (Lm (Mx X x0 x τ) * ((mat x0 τ)⁻¹ * mat x τ))
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Lm (Mx X x0 x τ))⁻¹, Matrix.nonsing_inv_mul _ hL, Matrix.one_mul,
    ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu0, Matrix.one_mul]
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
