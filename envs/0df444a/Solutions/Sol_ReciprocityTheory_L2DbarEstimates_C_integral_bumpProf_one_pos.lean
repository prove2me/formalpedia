-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.integral_bumpProf_one_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:02:39.784618+00:00
-- url     : https://prove2.me/submissions/5dc6ac6e-45c4-4f88-bc37-547099ad08d9

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralBumpProfOnePos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
variable {n : ℕ}
private lemma bumpProf_eq_zero_of_half_lt {t s : ℝ} (ht : 0 < t) (hs : t / 2 < s) : bumpProf t s = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have h1 : 1 / 2 < s / t := by rw [lt_div_iff₀ ht]; linarith
  nlinarith
private lemma continuous_bumpProf_norm (n : ℕ) (t : ℝ) : Continuous (fun z : V n => bumpProf t ‖z‖) :=
  Real.smoothTransition.continuous.comp (by fun_prop)
end ReciprocityTheory.L2DbarEstimates.C
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution (n : ℕ) : 0 < ∫ z : V n, bumpProf 1 ‖z‖ := by
  have hcs : HasCompactSupport (fun z : V n => bumpProf 1 ‖z‖) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : V n) (1 / 2)) fun z hz => ?_
    rw [mem_closedBall, dist_zero_right, not_le] at hz
    exact bumpProf_eq_zero_of_half_lt one_pos hz
  refine (continuous_bumpProf_norm n 1).integral_pos_of_hasCompactSupport_nonneg_nonzero hcs
    (fun z => Real.smoothTransition.nonneg _) (x := 0) ?_
  simp [bumpProf]
end ReciprocityTheory.L2DbarEstimates.C
