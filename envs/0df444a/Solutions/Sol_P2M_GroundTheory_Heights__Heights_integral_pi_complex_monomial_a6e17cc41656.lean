-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_integral_pi_complex_monomial_a6e17cc41656
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:09:27.931118+00:00
-- url     : https://prove2.me/submissions/bbe11b43-0ec6-455b-b426-364afd7ee05a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FubiniStudyIntegral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_lintegral_pi_complex_monomial_e34694584652

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Set Filter Topology Real
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (k N : ℕ) (b : Fin N → ℕ) (c : ℝ) (hc : 0 < c) :
    Integrable (fun z : Fin N → ℂ => (∏ j, ‖z j‖ ^ (2 * b j)) /
        (c + ∑ j, ‖z j‖ ^ 2) ^ (∑ j, b j + N + 1 + k)) ∧
    ∫ z : Fin N → ℂ, (∏ j, ‖z j‖ ^ (2 * b j)) / (c + ∑ j, ‖z j‖ ^ 2) ^ (∑ j, b j + N + 1 + k) =
      π ^ N * (∏ j, ((b j).factorial : ℝ)) * k.factorial / (∑ j, b j + N + k).factorial /
        c ^ (k + 1) := by
  have hnn : ∀ z : Fin N → ℂ, 0 ≤ (∏ j, ‖z j‖ ^ (2 * b j)) /
      (c + ∑ j, ‖z j‖ ^ 2) ^ (∑ j, b j + N + 1 + k) := fun z => by positivity
  have hm : AEStronglyMeasurable (fun z : Fin N → ℂ => (∏ j, ‖z j‖ ^ (2 * b j)) /
      (c + ∑ j, ‖z j‖ ^ 2) ^ (∑ j, b j + N + 1 + k)) := by
    exact (by fun_prop : Measurable _).aestronglyMeasurable
  refine ⟨⟨hm, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hnn), lintegral_pi_complex_monomial k N b c hc]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn) hm,
      lintegral_pi_complex_monomial k N b c hc, ENNReal.toReal_ofReal (by positivity)]
end GroundTheory.Heights₂.Heights
