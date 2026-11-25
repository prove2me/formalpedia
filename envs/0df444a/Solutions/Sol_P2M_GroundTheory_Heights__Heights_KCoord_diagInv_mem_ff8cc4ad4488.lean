-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KCoord_diagInv_mem_ff8cc4ad4488
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:00:39.674862+00:00
-- url     : https://prove2.me/submissions/73372426-22a9-4b43-995b-a50d6a512165

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_CoordSiegel

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
variable {g : ℕ}
open GroundTheory.Heights₂.Heights.KCoord
namespace GroundTheory.Heights₂.Heights.KCoord
theorem _root_.solution (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.PosDef) :
    diagInv Y ∈ symplecticGroup (Fin g) ℝ := by
  have hdet : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).1 hY.isUnit
  have hYt : Yᵀ = Y := by
    have := hY.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hYit : Y⁻¹ᵀ = Y⁻¹ := by rw [Matrix.transpose_nonsing_inv, hYt]
  rw [SymplecticGroup.mem_iff]
  simp [diagInv, Matrix.J, fromBlocks_transpose, fromBlocks_multiply, hYt, hYit,
    Matrix.nonsing_inv_mul _ hdet, Matrix.mul_nonsing_inv _ hdet]
end GroundTheory.Heights₂.Heights.KCoord
