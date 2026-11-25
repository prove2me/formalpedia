-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.lminor_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:31:52.69822+00:00
-- url     : https://prove2.me/submissions/51130550-6acc-4246-b886-67b8bd308dcc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
  Metric Polynomial
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {x0 : Frame X.Ψ r}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
theorem _root_.solution (k : Fin (r + 1)) : lminor (1 : Matrix (Fin r) (Fin r) ℂ) k = 1 := by
  unfold lminor
  rw [Matrix.submatrix_one _ (Fin.castLE_injective _), Matrix.det_one]
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
