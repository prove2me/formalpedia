-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCBounds_posDef_of_ge_c2392ab1fa43
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:42:35.030861+00:00
-- url     : https://prove2.me/submissions/3b509e96-33e0-4f6d-87d7-26b3a86da3b9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_dot_self_nonneg_1b107a996ff0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_quad_sub_smul_one_15ab2baf7d6c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_quad_nonneg_28912038225c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_transpose_of_posSemidef_d635eeb9d649

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
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} {c : ℝ}
    (hc : 0 < c) (h : (A - c • (1 : Matrix ι ι ℝ)).PosSemidef) : A.PosDef := by
  have hs : Aᵀ = A := by
    have := transpose_of_posSemidef h
    rw [transpose_sub, transpose_smul, transpose_one] at this
    exact sub_left_injective this
  refine posDef_iff_dotProduct_mulVec.mpr ⟨(conjTranspose_eq_transpose_of_trivial A).trans hs,
    fun x hx => ?_⟩
  have h1 := quad_nonneg h x
  rw [quad_sub_smul_one] at h1
  have h2 : 0 < x ⬝ᵥ x := by
    rcases (dot_self_nonneg x).lt_or_eq with h3 | h3
    · exact h3
    · exact absurd (dotProduct_self_eq_zero.mp h3.symm) hx
  simpa using (by nlinarith : 0 < x ⬝ᵥ (A *ᵥ x))
end GroundTheory.Heights₂.Heights.MCBounds
