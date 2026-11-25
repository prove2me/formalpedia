-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.unipotentFrame_transpose_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:31:30.37817+00:00
-- url     : https://prove2.me/submissions/be704eb9-8e7f-4d2e-ab6e-e917f224fb20

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_det_unipotentFrame_eq_one

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
theorem _root_.solution (z : V (nd X)) (τ : X.Ψ) : (n1 X z τ)ᵀ * Zt X z τ = (Wm X z τ)ᵀ := by
  have hdet : IsUnit (n1 X z τ).det := by rw [det_unipotentFrame_eq_one]; exact isUnit_one
  unfold Zt
  rw [Matrix.transpose_mul, ← Matrix.mul_assoc, ← Matrix.transpose_mul,
    Matrix.nonsing_inv_mul _ hdet, Matrix.transpose_one, Matrix.one_mul]
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
