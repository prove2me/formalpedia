-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCCusp_dot_mulVec_symm_9b8f1a0cd591
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:11.1069+00:00
-- url     : https://prove2.me/submissions/d2f02db8-2690-4dd6-afdc-9bae7a591c73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_HermValueIsLeast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCCusp
open Matrix GroundTheory.Heights₂.Heights.MCSchur
noncomputable section
variable {ι : Type*} [Fintype ι]
namespace GroundTheory.Heights₂.Heights.MCCusp
theorem _root_.solution {Z : Matrix ι ι ℝ} (hZ : Zᵀ = Z) (u w : ι → ℝ) :
    u ⬝ᵥ (Z *ᵥ w) = w ⬝ᵥ (Z *ᵥ u) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hZ, dotProduct_comm]
end GroundTheory.Heights₂.Heights.MCCusp
