-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.det_ne_of_orth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:23.334457+00:00
-- url     : https://prove2.me/submissions/08949cd8-d019-4a07-804b-58210d582421

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_gram_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates
  ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
theorem _root_.solution {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (τ : X.Ψ) : (mat x0 τ).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (ho τ)
  have h2 : gram τ.1 X.Gm (mat x0 τ) =
      (mat x0 τ)ᵀ * gram τ.1 X.Gm 1 * (mat x0 τ).map (starRingEnd ℂ) := by
    rw [← ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_mul, Matrix.one_mul]
  rw [h2, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h, zero_mul, zero_mul,
    Matrix.det_diagonal] at h1
  refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h1.symm
  unfold sgn
  split_ifs <;> norm_num
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
