-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KThetaSummandNorm_qf_add_272ec1b90821
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:01:32.85228+00:00
-- url     : https://prove2.me/submissions/be61fe82-41fc-4c5c-b868-643235b7a2a9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PThetaSummandNorm

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
open GroundTheory.Heights₂.Heights.KThetaSummandNorm
namespace GroundTheory.Heights₂.Heights.KThetaSummandNorm
theorem _root_.solution {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.IsSymm) (w u : Fin g → ℝ) :
    qf Y (w + u) = qf Y w + 2 * (w ⬝ᵥ (Y *ᵥ u)) + qf Y u := by
  have h : u ⬝ᵥ (Y *ᵥ w) = w ⬝ᵥ (Y *ᵥ u) := by
    rw [dotProduct_mulVec, ← vecMul_transpose, hY.eq, dotProduct_comm]
  simp only [qf, mulVec_add, dotProduct_add, add_dotProduct, h]
  ring
end GroundTheory.Heights₂.Heights.KThetaSummandNorm
