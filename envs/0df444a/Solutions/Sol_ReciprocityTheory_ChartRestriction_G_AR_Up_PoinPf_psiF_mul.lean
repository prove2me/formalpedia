-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.psiF_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:36:11.990796+00:00
-- url     : https://prove2.me/submissions/3e517c21-0781-4c3f-af74-d0967c8ddf25

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfI
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_kaY_pos


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
theorem _root_.solution (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (P : Frame X.Ψ r → ℂ)
    (W : Frame X.Ψ r → ℝ≥0∞) {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    psiF X x0 bb P W y * ENNReal.ofReal (kaY X x0 bb y) = ‖P y‖ₑ ^ 2 * W y := by
  unfold psiF
  rw [Set.indicator_of_mem hy, ENNReal.div_mul_cancel (ENNReal.ofReal_pos.2 (kaY_pos X x0 bb y)).ne'
    ENNReal.ofReal_ne_top]
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
