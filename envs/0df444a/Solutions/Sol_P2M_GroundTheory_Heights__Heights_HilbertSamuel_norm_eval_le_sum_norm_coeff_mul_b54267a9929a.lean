-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_norm_eval_le_sum_norm_coeff_mul_b54267a9929a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:28.786015+00:00
-- url     : https://prove2.me/submissions/ee6d7ac2-1faa-4e69-8ceb-d5a55f9c0d37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StMonicRootGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_PMonicRootGrowth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Finset
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {d : ℕ} (a : MvPolynomial (Fin d) ℂ) (y : Fin d → ℂ) :
    ‖eval y a‖ ≤ (∑ s ∈ a.support, ‖coeff s a‖) * (1 + ‖y‖) ^ a.totalDegree := by
  have h1 : (1 : ℝ) ≤ 1 + ‖y‖ := le_add_of_nonneg_right (norm_nonneg _)
  rw [eval_eq, sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun s hs ↦ ?_)
  rw [norm_mul, norm_prod]
  gcongr
  calc ∏ i ∈ s.support, ‖y i ^ s i‖
      ≤ ∏ i ∈ s.support, (1 + ‖y‖) ^ s i := by
        gcongr with i
        rw [norm_pow]
        gcongr
        exact (norm_le_pi_norm y i).trans (le_add_of_nonneg_left zero_le_one)
    _ = (1 + ‖y‖) ^ (s.sum fun _ e ↦ e) := prod_pow_eq_pow_sum _ _ _
    _ ≤ (1 + ‖y‖) ^ a.totalDegree := pow_le_pow_right₀ h1 (le_totalDegree hs)
end GroundTheory.Heights₂.Heights.HilbertSamuel
