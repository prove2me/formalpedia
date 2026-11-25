-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.OFC.unipotentFrame_scaling_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:33:43.672624+00:00
-- url     : https://prove2.me/submissions/a259bc5d-8c22-4872-be7a-67dcdf40db64

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
theorem _root_.solution (t : ℝ) (z : V (nd X)) (τ : X.Ψ) : ExF.n1 X (S1 X t z) τ = ExF.n1 X z τ := by
  ext a b
  have ha := a.isLt
  simp only [ExF.Wm, ExF.n1, ExF.nM, mat, nmat, Matrix.submatrix_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, WithLp.ofLp_toLp, PiLp.toLp_apply, S1]
  split_ifs with h1 h2 <;>
    first
    | rfl
    | (exfalso
       simp only [isW, Equiv.symm_apply_apply, Fin.coe_castLE] at *
       omega)
end ReciprocityTheory.ChartRestriction.G.AR.Up.OFC
