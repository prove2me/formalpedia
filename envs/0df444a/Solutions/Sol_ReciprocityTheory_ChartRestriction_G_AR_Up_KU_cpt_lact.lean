-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.KU.cpt_lact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:42.945335+00:00
-- url     : https://prove2.me/submissions/3929645d-db7b-415f-9d57-5c6fe85414d8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.KU
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU
theorem _root_.solution (X : Data E r) (γ : GL (Fin r) E) (x0 : Frame X.Ψ r) (z : V (nd X)) :
    cpt X (lact γ x0) z = lact γ (cpt X x0 z) := by
  funext τ
  show (((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x0 τ) * mat (nmat X z) τ : Matrix (Fin r) (Fin r) ℂ) =
    (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x0 τ * mat (nmat X z) τ)
  rw [Matrix.mul_assoc]
end ReciprocityTheory.ChartRestriction.G.AR.Up.KU
