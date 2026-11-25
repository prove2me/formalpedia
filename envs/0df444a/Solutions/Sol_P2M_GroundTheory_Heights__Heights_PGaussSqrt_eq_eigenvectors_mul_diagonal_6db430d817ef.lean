-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PGaussSqrt_eq_eigenvectors_mul_diagonal_6db430d817ef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:46:02.895892+00:00
-- url     : https://prove2.me/submissions/166855ff-431e-47f6-8944-356a57ed5678

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussSqrt

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
open GroundTheory.Heights₂.Heights.PGaussSqrt
namespace GroundTheory.Heights₂.Heights.PGaussSqrt
theorem _root_.solution {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} (hH : Y.IsHermitian) :
    Y = (hH.eigenvectorUnitary : Matrix (Fin g) (Fin g) ℝ) * diagonal hH.eigenvalues *
      (hH.eigenvectorUnitary : Matrix (Fin g) (Fin g) ℝ)ᵀ := by
  conv_lhs => rw [hH.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  rfl
end GroundTheory.Heights₂.Heights.PGaussSqrt
