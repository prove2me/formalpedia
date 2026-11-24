-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCBounds_posSemidef_of_real_0d966a4c7af2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:14.644536+00:00
-- url     : https://prove2.me/submissions/15130783-551d-45ea-b58d-62f1bcd5f3de

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
theorem _root_.solution {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hs : Aᵀ = A)
    (h : ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x)) : A.PosSemidef :=
  PosSemidef.of_dotProduct_mulVec_nonneg
    ((conjTranspose_eq_transpose_of_trivial A).trans hs) (by simpa using h)
end GroundTheory.Heights₂.Heights.MCBounds
