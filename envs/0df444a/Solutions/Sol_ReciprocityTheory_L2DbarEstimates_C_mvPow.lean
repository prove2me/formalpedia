-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.mvPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:16:16.921609+00:00
-- url     : https://prove2.me/submissions/2916b25b-794b-4c1f-8091-1baa83f20e03

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MvDivIntegrand
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_finrank_real_V

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution : MVPowStatement := by
  intro n s hn
  haveI : Nontrivial (V n) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_real_V]; omega)
  have hind : (ball (0 : V n) 1).indicator (fun z : V n => ‖z‖ ^ (-2 * s)) =
      fun z => (Iio (1 : ℝ)).indicator (fun y : ℝ => y ^ (-2 * s)) ‖z‖ := by
    funext z
    by_cases h : ‖z‖ < 1 <;> simp [Set.indicator, mem_ball_zero_iff, h]
  rw [← integrable_indicator_iff measurableSet_ball, hind, integrable_fun_norm_addHaar,
    finrank_real_V]
  have hfun : (fun y : ℝ => y ^ (2 * n - 1) • (Iio (1 : ℝ)).indicator (fun y : ℝ => y ^ (-2 * s)) y) =
      (Iio (1 : ℝ)).indicator (fun y : ℝ => y ^ (2 * n - 1) * y ^ (-2 * s)) := by
    funext y
    simp only [indicator_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hfun, IntegrableOn, integrable_indicator_iff measurableSet_Iio, IntegrableOn,
    Measure.restrict_restrict measurableSet_Iio, Set.inter_comm, Set.Ioi_inter_Iio, ← IntegrableOn]
  have hcongr : EqOn (fun y : ℝ => y ^ (2 * n - 1) * y ^ (-2 * s))
      (fun y : ℝ => y ^ ((2 * n : ℝ) - 1 - 2 * s)) (Ioo 0 1) := by
    intro y hy
    have hy0 : 0 < y := hy.1
    simp only
    rw [← Real.rpow_natCast, ← Real.rpow_add hy0]
    congr 1
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]
    push_cast
    ring
  rw [integrableOn_congr_fun hcongr measurableSet_Ioo,
    intervalIntegral.integrableOn_Ioo_rpow_iff one_pos]
  constructor <;> intro h <;> linarith
end ReciprocityTheory.L2DbarEstimates.C
