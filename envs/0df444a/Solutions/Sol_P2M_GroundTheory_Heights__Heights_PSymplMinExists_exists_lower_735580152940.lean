-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplMinExists_exists_lower_735580152940
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:31:42.848866+00:00
-- url     : https://prove2.me/submissions/76621cf2-1d72-4587-b617-a6590c3d9521

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplMinExists
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplMinExists_qf_smul_c52cc2b03309
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplMinExists_continuous_qf_a86f9130f63a

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
open Matrix
open GroundTheory.Heights₂.Heights.PSymplMinExists
variable {ι : Type} [Fintype ι]
namespace GroundTheory.Heights₂.Heights.PSymplMinExists
theorem _root_.solution [DecidableEq ι] [Nonempty ι] (G : Matrix ι ι ℝ) (hG : G.PosDef) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ x : ι → ℝ, μ * ‖x‖ ^ 2 ≤ qf G x := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hpos : ∀ x : ι → ℝ, x ≠ 0 → 0 < qf G x := fun x hx => by
    simpa [qf] using hG.dotProduct_mulVec_pos hx
  have hK : IsCompact (Metric.sphere (0 : ι → ℝ) 1) := isCompact_sphere 0 1
  have hne : (Metric.sphere (0 : ι → ℝ) 1).Nonempty :=
    ⟨Pi.single i₀ 1, by simp [Pi.norm_single]⟩
  obtain ⟨u, hu, hmin⟩ := hK.exists_isMinOn hne (continuous_qf G).continuousOn
  refine ⟨qf G u, hpos u ?_, fun x => ?_⟩
  · rintro rfl
    simp at hu
  · by_cases hx : x = 0
    · subst hx
      simp [qf]
    · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hy : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : ι → ℝ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have h1 : qf G u ≤ qf G (‖x‖⁻¹ • x) := isMinOn_iff.mp hmin _ hy
      calc qf G u * ‖x‖ ^ 2 ≤ qf G (‖x‖⁻¹ • x) * ‖x‖ ^ 2 := by gcongr
        _ = qf G x := by
          rw [qf_smul]
          field_simp
end GroundTheory.Heights₂.Heights.PSymplMinExists
