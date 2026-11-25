-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FirstCoordinateBound_intersectionNumber_baseChange_a7c2d8d1f691
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:25:29.183655+00:00
-- url     : https://prove2.me/submissions/234ea21a-4822-4967-9b58-f5561431c30d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_CoordFirst
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KCoord_sq_coord_le_d1ab1fa771ab

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
namespace GroundTheory.Heights₂.Heights
namespace FirstCoordinateBound
theorem _root_.solution : FirstCoordinateBound.Statement := by
  intro g _ Y hY v
  have h := KCoord.sq_coord_le Y hY 0 v
  rw [div_le_iff₀ hY.inv.diag_pos, mul_comm]
  exact h
end FirstCoordinateBound
end GroundTheory.Heights₂.Heights
