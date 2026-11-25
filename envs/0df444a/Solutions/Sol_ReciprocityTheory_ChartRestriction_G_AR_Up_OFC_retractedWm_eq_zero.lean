-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.OFC.retractedWm_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:33:38.765796+00:00
-- url     : https://prove2.me/submissions/cb07b568-9f15-4b91-ba80-0461ac0e0581

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OmFConnPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OFC
open NumberField Complex Matrix Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OFC
theorem _root_.solution (t : ℝ) (z : V (nd X)) (τ : X.Ψ) : ExF.Wm X (S2 X t z) τ = 0 := by
  ext m c
  have hc := c.isLt
  have hlt : Fin.castLE X.p0_le c < ExF.qI X m := by
    rw [Fin.lt_def]
    simp only [Fin.coe_castLE, ExF.qI]
    omega
  simp only [ExF.Wm, ExF.n1, ExF.nM, mat, nmat, Matrix.submatrix_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, WithLp.ofLp_toLp, PiLp.toLp_apply, S2, dif_pos hlt, Matrix.zero_apply]
  rw [if_pos]
  simp only [isW, Equiv.symm_apply_apply, ExF.qI, Fin.coe_castLE]
  omega
end ReciprocityTheory.ChartRestriction.G.AR.Up.OFC
