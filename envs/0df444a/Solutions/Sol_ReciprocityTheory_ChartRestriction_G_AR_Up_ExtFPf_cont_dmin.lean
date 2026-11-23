-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.cont_dmin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:17.37315+00:00
-- url     : https://prove2.me/submissions/60ae5d06-3390-492d-b17f-f60b76cfce36

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
theorem _root_.solution (τ : X.Ψ) (i : Fin (r + 1)) : Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
  unfold dmin lminor gram hermC col mat
  first
    | fun_prop
    | (apply Continuous.matrix_det; apply Continuous.matrix_submatrix; fun_prop)
    | continuity
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
