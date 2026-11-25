-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KThetaNormMajorant_isSymm_of_posDef_17a751f32486
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:01:25.694455+00:00
-- url     : https://prove2.me/submissions/94a7b1e0-0044-4c34-b8b2-ff6ee72ba541

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ThetaGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PThetaNormMajorant

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
open GroundTheory.Heights₂.Heights.KThetaNormMajorant
namespace GroundTheory.Heights₂.Heights.KThetaNormMajorant
theorem _root_.solution {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} (hY : Y.PosDef) : Y.IsSymm := by
  have h := hY.isHermitian
  unfold Matrix.IsHermitian at h
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h
end GroundTheory.Heights₂.Heights.KThetaNormMajorant
