-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.mv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:30:31.941644+00:00
-- url     : https://prove2.me/submissions/3c2faa95-8b3a-4664-92ca-99ddc1389994

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_NormFibrations_MvBlowup
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_mv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Metric Filter Topology
open scoped ENNReal
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution (n : ℕ) : MVStatement n := by
  intro R u ρ hu hρ hR
  have h := C.mv n 0 R u ρ hu hρ
  simp only [sub_zero] at h
  have hc : ∀ x : ℂ, ENNReal.ofReal (‖x‖ ^ 2) = ‖x‖ₑ ^ 2 := fun x => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have hz : ∀ y : V n, y ∉ Metric.ball (0 : V n) R → ρ ‖y‖ = 0 := by
    intro y hy
    apply hR
    simpa [Metric.mem_ball, dist_zero_right, not_lt] using hy
  have e1 : ∫⁻ y in Metric.ball (0 : V n) R, ρ ‖y‖ = ∫⁻ y : V n, ρ ‖y‖ := by
    apply setLIntegral_eq_of_support_subset
    intro y hy
    by_contra hb
    exact hy (hz y hb)
  have e2 : ∫⁻ y in Metric.ball (0 : V n) R, ‖u y‖ₑ ^ 2 * ρ ‖y‖ =
      ∫⁻ y : V n, ‖u y‖ₑ ^ 2 * ρ ‖y‖ := by
    apply setLIntegral_eq_of_support_subset
    intro y hy
    by_contra hb
    exact hy (by simp [hz y hb])
  simp_rw [hc]
  rw [← e1, ← e2]
  exact h
end ReciprocityTheory.L2DbarEstimates
