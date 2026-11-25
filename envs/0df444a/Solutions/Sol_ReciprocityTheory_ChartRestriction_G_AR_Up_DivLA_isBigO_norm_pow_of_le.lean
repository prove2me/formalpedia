-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.isBigO_norm_pow_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:52:31.222668+00:00
-- url     : https://prove2.me/submissions/5201d7d8-7de7-456b-826b-39f16dadc719

import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_NormFibrations_MvBlowup
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_LintegralBallRpowLtTop
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Asymptotics
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
theorem _root_.solution {F : Type*} [NormedAddCommGroup F] {k d : ℕ} (h : k ≤ d) :
    (fun y : F => ‖y‖ ^ d) =O[𝓝 0] (fun y => ‖y‖ ^ k) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Metric.ball_mem_nhds (0 : F) one_pos] with y hy
  rw [mem_ball_zero_iff] at hy
  simp only [norm_pow, norm_norm, one_mul]
  exact pow_le_pow_of_le_one (norm_nonneg _) hy.le h
end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
