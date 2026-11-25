-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KCoord_siegelGram_eq_e89b1c54405c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:00:56.235463+00:00
-- url     : https://prove2.me/submissions/70af81e8-bcd2-418a-b23e-a16b724d7139

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
theorem _root_.solution (X Y : Matrix (Fin g) (Fin g) ℝ) (hX : X.IsSymm) :
    siegelGram X Y = (unip X)ᵀ * diagInv Y * unip X := by
  have hXt : Xᵀ = X := hX
  simp [siegelGram, unip, diagInv, fromBlocks_transpose, fromBlocks_multiply, hXt, add_comm]
end GroundTheory.Heights₂.Heights.KCoord
