-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.FM.KR_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:32:21.964457+00:00
-- url     : https://prove2.me/submissions/f87469be-d1e6-4b6f-a596-f3b1eff1d2fd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_continuous_jacU


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
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FM
theorem _root_.solution {R0 : ℝ} (hR0 : 0 ≤ R0) : KR X R0 < ⊤ := by
  have hc : IsCompact (SR X R0) := by
    have h : SR X R0 = Set.pi Set.univ (fun _ => Metric.closedBall (0 : ℂ) R0) := by
      ext c
      simp [SR, Set.mem_pi]
    rw [h]
    exact isCompact_univ_pi fun _ => isCompact_closedBall 0 R0
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn
    ((Complex.continuous_normSq.comp continuous_jacU).continuousOn)
  calc KR X R0 ≤ ∫⁻ _ in SR X R0, ENNReal.ofReal C := by
        unfold KR
        refine setLIntegral_mono measurable_const fun y hy => ENNReal.ofReal_le_ofReal ?_
        have := hC y hy
        rw [Real.norm_eq_abs] at this
        exact le_trans (le_abs_self _) this
    _ = ENNReal.ofReal C * volume (SR X R0) := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hc.measure_lt_top
end ReciprocityTheory.ChartRestriction.G.AR.Up.FM
