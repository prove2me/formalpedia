-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.kaY_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:43:08.631071+00:00
-- url     : https://prove2.me/submissions/9bd1f172-e6cc-4d40-85b4-709fdf2fcd6f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfI

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
theorem _root_.solution (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (y : Frame X.Ψ r) :
    ENNReal.ofReal (kaY X x0 bb y) ^ (1 / 2 : ℝ) = ENNReal.ofReal (kaY X x0 (bb / 2) y) := by
  unfold kaY
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num), ← Real.exp_mul]
  congr 2
  ring
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
