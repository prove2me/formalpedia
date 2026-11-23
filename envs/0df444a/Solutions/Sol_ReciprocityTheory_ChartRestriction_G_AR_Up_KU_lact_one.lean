-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.KU.lact_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:38.960725+00:00
-- url     : https://prove2.me/submissions/9caa51c2-f453-4083-9e3b-48a2c284ce99

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
theorem _root_.solution (X : Data E r) (x : Frame X.Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  show (((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]; rfl
end ReciprocityTheory.ChartRestriction.G.AR.Up.KU
