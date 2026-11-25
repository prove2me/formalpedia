-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_exists_norm_le_norm_shifted_e469ac1e280a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:28:16.808156+00:00
-- url     : https://prove2.me/submissions/065fd5da-f56d-4377-9090-33ed243c2b9c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsKernelProjMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PKernelProjMeasurable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_re_inner_shifted_88976e2f9300

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
open MeasureTheory Filter Topology ContinuousLinearMap
noncomputable section
open GroundTheory.Heights₂.Heights.KernelProjMeasurable
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
namespace GroundTheory.Heights₂.Heights.KernelProjMeasurable
theorem _root_.solution (A : E →L[ℂ] F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε → ∀ u ∈ (LinearMap.ker (A : E →ₗ[ℂ] F))ᗮ, ‖u‖ ≤ C * ‖shifted A ε u‖ := by
  set K := LinearMap.ker (A : E →ₗ[ℂ] F)
  have hinj : Function.Injective ((A : E →ₗ[ℂ] F).comp Kᗮ.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h1 : (u : E) ∈ K := hu
    have h2 : (u : E) ∈ K ⊓ Kᗮ := ⟨h1, u.2⟩
    rw [K.inf_orthogonal_eq_bot, Submodule.mem_bot] at h2
    exact Subtype.ext h2
  obtain ⟨c, -, hc⟩ := ((A : E →ₗ[ℂ] F).comp Kᗮ.subtype).injective_iff_antilipschitz.1 hinj
  refine ⟨(c : ℝ) ^ 2, sq_nonneg _, fun ε hε u hu => ?_⟩
  have h1 : ‖u‖ ≤ c * ‖A u‖ := by
    simpa using hc.le_mul_norm (map_zero _) ⟨u, hu⟩
  have h2 := re_inner_shifted A ε u
  have h3 := re_inner_le_norm (𝕜 := ℂ) u (shifted A ε u)
  have hc0 : (0 : ℝ) ≤ c := c.2
  rcases eq_or_lt_of_le (norm_nonneg u) with h | h
  · rw [← h]; positivity
  · have hAu : ‖u‖ ^ 2 ≤ (c : ℝ) ^ 2 * ‖A u‖ ^ 2 := by
      have := mul_le_mul h1 h1 (norm_nonneg _) (by positivity)
      nlinarith
    have h4 : (c : ℝ) ^ 2 * ‖A u‖ ^ 2 ≤ (c : ℝ) ^ 2 * (‖u‖ * ‖shifted A ε u‖) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      nlinarith [mul_nonneg hε (sq_nonneg ‖u‖)]
    have h5 : ‖u‖ * ‖u‖ ≤ ((c : ℝ) ^ 2 * ‖shifted A ε u‖) * ‖u‖ := by nlinarith
    exact le_of_mul_le_mul_right h5 h
end GroundTheory.Heights₂.Heights.KernelProjMeasurable
