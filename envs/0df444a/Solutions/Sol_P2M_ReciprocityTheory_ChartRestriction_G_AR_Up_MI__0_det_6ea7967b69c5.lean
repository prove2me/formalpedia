-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI__0_det_6ea7967b69c5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:06:04.205602+00:00
-- url     : https://prove2.me/submissions/5615f60f-76fc-416a-8176-8ce3670e761a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfI
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_bOf_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution {y : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) : (β0 X y τ).det ≠ 0 := by
  intro h0
  have h1 := Matrix.det_mul (mat (bOf X y) τ) (mat (bOf X y) τ)⁻¹
  rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (bOf_det X hy τ)), Matrix.det_one] at h1
  have h0' : ((mat (bOf X y) τ)⁻¹).det = 0 := h0
  rw [h0', mul_zero] at h1
  exact one_ne_zero h1
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
