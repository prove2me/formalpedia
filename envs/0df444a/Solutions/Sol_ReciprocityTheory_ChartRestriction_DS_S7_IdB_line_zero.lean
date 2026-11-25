-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.IdB.line_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:15:18.817277+00:00
-- url     : https://prove2.me/submissions/2fd1420b-c266-4bd4-b124-1146b7f89ce8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IdThmB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.IdB
namespace ReciprocityTheory.ChartRestriction.DS.S7.IdB
theorem _root_.solution {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (g : ℂ → F)
    (hg : ∀ s : ℂ, ‖s‖ < 2 → DifferentiableAt ℂ g s) (hr : ∀ t : ℝ, |t| < 2 → g t = 0) :
    g Complex.I = 0 := by
  have hDO : DifferentiableOn ℂ g (Metric.ball 0 2) := fun s hs =>
    (hg s (by simpa using hs)).differentiableWithinAt
  have han := hDO.analyticOnNhd Metric.isOpen_ball
  have ht : Filter.Tendsto (fun t : ℝ => (t : ℂ)) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall fun t ht => by simpa using ht
  have hev : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) {0}ᶜ, g (t : ℂ) = 0 := by
    have h2 : ∀ᶠ t in nhds (0 : ℝ), |t| < 2 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) two_pos] with t ht
      simpa [Real.dist_eq] using ht
    exact (Filter.Eventually.filter_mono nhdsWithin_le_nhds h2).mono fun t h => hr t h
  have hfreq : ∃ᶠ s in nhdsWithin (0 : ℂ) {0}ᶜ, g s = 0 := ht.frequently hev.frequently
  have hz := han.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_ball (0 : ℂ) 2).isPreconnected
    (Metric.mem_ball_self two_pos) hfreq
  have hI : Complex.I ∈ Metric.ball (0 : ℂ) 2 := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_I]
    norm_num
  simpa using hz hI
end ReciprocityTheory.ChartRestriction.DS.S7.IdB
