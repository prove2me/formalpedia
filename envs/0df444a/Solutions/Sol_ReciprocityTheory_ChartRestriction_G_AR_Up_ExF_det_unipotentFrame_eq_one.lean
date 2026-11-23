-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.det_unipotentFrame_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:33.364133+00:00
-- url     : https://prove2.me/submissions/b1ed4eb5-6002-4707-a131-c0c2c8463197

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_nM_upper
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_nM_diag

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
theorem _root_.solution (z : V (nd X)) (τ : X.Ψ) : (n1 X z τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [n1, nM_diag]
  · unfold Matrix.IsLowerTriangular Matrix.BlockTriangular
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    simp only [n1, Matrix.submatrix_apply]
    apply nM_upper X z τ
    rw [Fin.lt_iff_val_lt_val] at hij' ⊢
    simpa using hij'
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
