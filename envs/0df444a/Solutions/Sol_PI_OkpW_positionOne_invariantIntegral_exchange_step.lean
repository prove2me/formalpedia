-- Prove2me | solution 1 for PI.OkpW.positionOne_invariantIntegral_exchange_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:59:26.044194+00:00
-- url     : https://prove2.me/submissions/bc390741-e41c-484f-ba4f-69bf38e7c375

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_TeichNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_UltrametricPairEstimate
import Theorems.Thm_PI_OkpW_norm_p_cp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
noncomputable section
open PI PI.OkpW
variable {K : Type} [Field K] [NumberField K] {p : ℕ} [hp : Fact p.Prime]
namespace PI.OkpW
theorem _root_.solution (X T Y R : ℂ_[p]) (n : ℕ) (h1 : ‖T - X‖ ≤ (p : ℝ)⁻¹ ^ (n + 1))
    (h2 : ‖Y - R‖ ≤ (p : ℝ)⁻¹ ^ n) :
    ‖(X - (p : ℂ_[p]) * Y) - (T - (p : ℂ_[p]) * R)‖ ≤ (p : ℝ)⁻¹ ^ (n + 1) := by
  have e : (X - (p : ℂ_[p]) * Y) - (T - (p : ℂ_[p]) * R) = (X - T) - (p : ℂ_[p]) * (Y - R) := by ring
  rw [e, ← dist_eq_norm]
  refine (IsUltrametricDist.dist_triangle_max _ 0 _).trans (max_le ?_ ?_)
  · rw [dist_zero_right, norm_sub_rev]
    exact h1
  · rw [dist_zero_left, norm_mul, norm_p_cp, pow_succ']
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
end PI.OkpW
