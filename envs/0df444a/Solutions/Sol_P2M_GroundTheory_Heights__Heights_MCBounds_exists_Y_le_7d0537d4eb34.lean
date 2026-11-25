-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCBounds_exists_Y_le_7d0537d4eb34
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:22:46.687559+00:00
-- url     : https://prove2.me/submissions/48b6c47e-b97b-4f1e-a59a-caf350556ff8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Bounds
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_one_le_radius_6e45f36c6393
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_Y_transpose_d3179c735349
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_exists_bound_im_0_a87623faa71f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_quad_Y_le_6883bb1a140d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_dot_self_nonneg_1b107a996ff0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_entrySum_nonneg_e371d83920f8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_posSemidef_of_real_0d966a4c7af2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_quad_smul_one_sub_79ae7301e3b8


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCBounds
open Matrix
open scoped ComplexOrder
noncomputable section
variable (D : PeriodChartData)
namespace GroundTheory.Heights₂.Heights.MCBounds
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ p ∈ D.K,
    ((C * D.radius p.1) • (1 : Matrix (Fin D.g) (Fin D.g) ℝ) - D.Y p.1).PosSemidef := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_imτ0 D
  have hβ : 0 ≤ ∑ j, entrySum (D.B j) := Finset.sum_nonneg fun j _ => entrySum_nonneg _
  refine ⟨M + ∑ j, entrySum (D.B j) + 1, by positivity, fun p hp => ?_⟩
  have hz : p.1 ∈ D.U := (D.K_subset hp).1
  have hr1 := one_le_radius D hz
  refine posSemidef_of_real ?_ fun x => ?_
  · rw [transpose_sub, transpose_smul, transpose_one, Y_transpose D hz]
  · rw [quad_smul_one_sub]
    have h := quad_Y_le D hz M (hM p hp) x
    have hxx := dot_self_nonneg x
    nlinarith
end GroundTheory.Heights₂.Heights.MCBounds
