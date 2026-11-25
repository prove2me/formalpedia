-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PGaussPoissonDual_qf_smul_e74801869daa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:45:53.913797+00:00
-- url     : https://prove2.me/submissions/2b19ef50-fde1-44ca-a43d-c0d6ed681eda

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
theorem _root_.solution {g : ℕ} (c : ℝ) (Y : Matrix (Fin g) (Fin g) ℝ) (w : Fin g → ℝ) :
    qf (c • Y) w = c * qf Y w := by
  rw [qf, qf, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
end GroundTheory.Heights₂.Heights.PGaussPoissonDual
