-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PGaussPoissonDual_dot_mulVec_self_baf40fed473c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:45:53.143519+00:00
-- url     : https://prove2.me/submissions/5d5e15fe-2dfe-4033-a146-6c4cf106fad0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussPoissonDual

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
open Matrix Real
noncomputable section
open GroundTheory.Heights₂.Heights.PGaussPoissonDual
namespace GroundTheory.Heights₂.Heights.PGaussPoissonDual
theorem _root_.solution {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (w : Fin g → ℝ) :
    (B *ᵥ w) ⬝ᵥ (B *ᵥ w) = qf (Bᵀ * B) w := by
  rw [qf, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec w Bᵀ, Matrix.vecMul_transpose]
end GroundTheory.Heights₂.Heights.PGaussPoissonDual
