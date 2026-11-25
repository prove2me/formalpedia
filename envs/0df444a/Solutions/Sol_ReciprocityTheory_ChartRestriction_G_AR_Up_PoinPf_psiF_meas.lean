-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.psiF_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:31:20.596925+00:00
-- url     : https://prove2.me/submissions/4d38bcda-201a-48ef-a975-2fa1ab8085a1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfI
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PairUnfoldPf_meas_indC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_meas_kaY


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
theorem _root_.solution (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ}
    {W : Frame X.Ψ r → ℝ≥0∞} (hP : IsBEq X la P) (hW : IsMetricW X la W) :
    Measurable (psiF X x0 bb P W) := by
  have h1 : Measurable (X.dom.indicator P) :=
    ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.meas_indC (X := X) hP.1.continuousOn
  unfold psiF
  exact ((h1.enorm.pow_const 2).mul hW.1).div (ENNReal.measurable_ofReal.comp (meas_kaY X x0 bb))
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
