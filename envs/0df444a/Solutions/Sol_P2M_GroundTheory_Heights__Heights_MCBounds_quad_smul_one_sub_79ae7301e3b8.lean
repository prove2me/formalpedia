-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCBounds_quad_smul_one_sub_79ae7301e3b8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:14.563634+00:00
-- url     : https://prove2.me/submissions/5164fabe-de8d-487b-adb8-f8af0e1956c6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY

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
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (l : ℝ)
    (x : ι → ℝ) : x ⬝ᵥ ((l • (1 : Matrix ι ι ℝ) - A) *ᵥ x) = l * (x ⬝ᵥ x) - x ⬝ᵥ (A *ᵥ x) := by
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
end GroundTheory.Heights₂.Heights.MCBounds
