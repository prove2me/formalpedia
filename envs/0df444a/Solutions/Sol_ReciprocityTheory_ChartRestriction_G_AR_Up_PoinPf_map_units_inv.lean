-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.map_units_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:34:39.13995+00:00
-- url     : https://prove2.me/submissions/853b101a-61a6-446c-9a74-df687a3d359c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
theorem _root_.solution (τ : E →+* ℂ) (γ : GL (Fin r) E) :
    ((↑(γ⁻¹) : Matrix (Fin r) (Fin r) E).map τ) = ((γ : Matrix (Fin r) (Fin r) E).map τ)⁻¹ := by
  have h : ((↑(γ⁻¹) : Matrix (Fin r) (Fin r) E).map τ) * ((γ : Matrix (Fin r) (Fin r) E).map τ) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul]
    exact Matrix.map_one _ (map_zero τ) (map_one τ)
  exact (Matrix.inv_eq_left_inv h).symm
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
