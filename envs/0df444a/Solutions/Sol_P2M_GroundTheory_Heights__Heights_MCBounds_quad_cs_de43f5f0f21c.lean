-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCBounds_quad_cs_de43f5f0f21c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:04.298797+00:00
-- url     : https://prove2.me/submissions/63b2db6f-05c5-4fbc-a020-8beb1b0d00fb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_quad_nonneg_28912038225c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_transpose_of_posSemidef_d635eeb9d649
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_quad_symm_4b25d90b3d61

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
noncomputable section
namespace GroundTheory.Heights₂.Heights.MCBounds
theorem _root_.solution {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (u v : ι → ℝ) :
    (u ⬝ᵥ (A *ᵥ v)) ^ 2 ≤ (u ⬝ᵥ (A *ᵥ u)) * (v ⬝ᵥ (A *ᵥ v)) := by
  have hvu := quad_symm (transpose_of_posSemidef hA) u v
  have key : ∀ t : ℝ, 0 ≤ (v ⬝ᵥ (A *ᵥ v)) * (t * t) + (2 * (u ⬝ᵥ (A *ᵥ v))) * t +
      u ⬝ᵥ (A *ᵥ u) := by
    intro t
    have h := quad_nonneg hA (u + t • v)
    simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, hvu] at h
    linarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith
end GroundTheory.Heights₂.Heights.MCBounds
