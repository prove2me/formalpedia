-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KCoord_unip_mem_d70ea5258c05
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:00:52.66086+00:00
-- url     : https://prove2.me/submissions/5b69d47a-6b66-44ec-81f2-79e401ad35bb

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
theorem _root_.solution (X : Matrix (Fin g) (Fin g) ℝ) (hX : X.IsSymm) :
    unip X ∈ symplecticGroup (Fin g) ℝ := by
  have hXt : Xᵀ = X := hX
  rw [SymplecticGroup.mem_iff]
  simp [unip, Matrix.J, fromBlocks_transpose, fromBlocks_multiply, hXt]
end GroundTheory.Heights₂.Heights.KCoord
