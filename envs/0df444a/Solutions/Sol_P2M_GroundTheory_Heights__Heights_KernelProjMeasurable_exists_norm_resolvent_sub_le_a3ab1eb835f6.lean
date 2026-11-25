-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_exists_norm_resolvent_sub_le_a3ab1eb835f6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:25:58.552845+00:00
-- url     : https://prove2.me/submissions/ffb126dd-700e-4a43-94c5-e432df18d550

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsKernelProjMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PKernelProjMeasurable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_inner_shifted_of_apply_eq_zero_645ecad0c612
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_shifted_apply_of_apply_eq_zero_c2e11a789312
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_isUnit_shifted_49b303e062a1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_exists_norm_le_norm_shifted_e469ac1e280a

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
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε →
      ‖resolvent A ε - (LinearMap.ker (A : E →ₗ[ℂ] F)).starProjection‖ ≤ C * ε := by
  obtain ⟨C, hC, hCb⟩ := exists_norm_le_norm_shifted A
  refine ⟨2 * C, fun ε hε => ?_⟩
  set K := LinearMap.ker (A : E →ₗ[ℂ] F)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  set u := (resolvent A ε - K.starProjection) v with hu_def
  have hinv : shifted A ε (Ring.inverse (shifted A ε) v) = v := by
    have := Ring.mul_inverse_cancel _ (isUnit_shifted A hε)
    exact congrArg (fun T : E →L[ℂ] E => T v) this
  have hPv : A (K.starProjection v) = 0 := K.starProjection_apply_mem v
  have hTu : shifted A ε u = (ε : ℂ) • (v - K.starProjection v) := by
    rw [hu_def, resolvent, sub_apply, smul_apply, map_sub, map_smul, hinv,
      shifted_apply_of_apply_eq_zero A ε hPv, smul_sub]
  have hu : u ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    have h1 := inner_shifted_of_apply_eq_zero A ε u hz
    rw [hTu, inner_smul_right,
      (Submodule.mem_orthogonal _ _).1 (K.sub_starProjection_mem_orthogonal v) z hz, mul_zero] at h1
    have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
    exact (mul_eq_zero.1 h1.symm).resolve_left hε'
  have hvP : ‖v - K.starProjection v‖ ≤ 2 * ‖v‖ :=
    (norm_sub_le _ _).trans (by linarith [K.norm_starProjection_apply_le v])
  calc ‖u‖ ≤ C * ‖shifted A ε u‖ := hCb ε hε.le u hu
    _ = C * (ε * ‖v - K.starProjection v‖) := by
      rw [hTu, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    _ ≤ C * (ε * (2 * ‖v‖)) := by gcongr
    _ = 2 * C * ε * ‖v‖ := by ring
end GroundTheory.Heights₂.Heights.KernelProjMeasurable
