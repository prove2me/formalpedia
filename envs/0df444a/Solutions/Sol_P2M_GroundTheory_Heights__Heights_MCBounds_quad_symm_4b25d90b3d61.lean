-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCBounds_quad_symm_4b25d90b3d61
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:10.822941+00:00
-- url     : https://prove2.me/submissions/9c9a70e5-99de-4257-8655-35e56e0b7033

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
theorem _root_.solution {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hs : Aᵀ = A) (u v : ι → ℝ) :
    v ⬝ᵥ (A *ᵥ u) = u ⬝ᵥ (A *ᵥ v) := by
  rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hs]
end GroundTheory.Heights₂.Heights.MCBounds
