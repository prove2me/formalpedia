-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.four_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:42:53.209784+00:00
-- url     : https://prove2.me/submissions/6b27335e-cb4c-49ef-bdbd-5fd63126c7cc

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourIndep
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fiBall_const

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Set
open scoped Interval
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (f : ℕ) : FOURIndepStatement f := by
  intro Ω h hΩ hpre hh hper b hb b' hb' ν
  cases f with
  | zero => rw [Subsingleton.elim b b']
  | succ n =>
    classical
    let F : (Fin (n + 1) → ℝ) → Bool := fun c => decide (fourCoeff h c ν = fourCoeff h b ν)
    have hF : ContinuousOn F Ω := by
      intro c hc
      apply ContinuousAt.continuousWithinAt
      obtain ⟨r, hr, hrc⟩ := fiBall_const hΩ hh hper ν c hc
      have hev : (fun _ => F c) =ᶠ[𝓝 c] F := by
        filter_upwards [Metric.ball_mem_nhds c hr] with d hd
        simp only [F, hrc d hd]
      exact continuousAt_const.congr hev
    have hcst : F b = F b' := hpre.constant hF hb hb'
    have hb'eq : F b' = true := by
      rw [← hcst]
      simp [F]
    simpa [F, eq_comm] using hb'eq
end ReciprocityTheory.L2DbarEstimates.Y
