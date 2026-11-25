-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.FM.continuous_UF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:30:35.93214+00:00
-- url     : https://prove2.me/submissions/a9813984-0700-44d7-becf-00c4c55af65a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPfC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.FM
open NumberField Matrix MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open scoped ENNReal NNReal
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
attribute [local instance] haarF haarIx
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FM
theorem _root_.solution : Continuous (UF X) := by
  apply continuous_pi
  intro τ
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  simp only [UF, Umat, Matrix.of_apply]
  by_cases hh : b < a
  · simp only [hh, not_true_eq_false, dite_false]
    exact continuous_const
  · simp only [hh, not_false_eq_true, dite_true]
    fun_prop
end ReciprocityTheory.ChartRestriction.G.AR.Up.FM
