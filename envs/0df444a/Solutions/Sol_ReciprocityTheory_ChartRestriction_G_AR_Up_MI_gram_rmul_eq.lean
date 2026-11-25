-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.gram_rmul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:06:07.876273+00:00
-- url     : https://prove2.me/submissions/c7c99d64-6307-4f82-be5d-8070ffd0f44c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfI
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_bOf_det
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_gram_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_ortho_bOf


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
theorem _root_.solution {y b : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (rmul y b) τ) = gramT X (β0 X y τ * mat b τ) := by
  have hB := bOf_det X hy τ
  have hyB : gram τ.1 X.Gm (mat y τ * mat (bOf X y) τ) = Jd X := ortho_bOf (X := X) hy τ
  have hy' : mat y τ = mat y τ * mat (bOf X y) τ * (mat (bOf X y) τ)⁻¹ := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hB), Matrix.mul_one]
  have hgy : gram τ.1 X.Gm (mat y τ) = (β0 X y τ)ᵀ * Jd X * (β0 X y τ).map (starRingEnd ℂ) := by
    rw [hy', gram_mul, hyB]
    rfl
  show gram τ.1 X.Gm (mat y τ * mat b τ) = _
  rw [gram_mul, hgy]
  unfold gramT
  rw [Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
