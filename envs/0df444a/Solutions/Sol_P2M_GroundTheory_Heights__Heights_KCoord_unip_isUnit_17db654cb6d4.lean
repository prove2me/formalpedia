-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KCoord_unip_isUnit_17db654cb6d4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:00:57.321533+00:00
-- url     : https://prove2.me/submissions/724fda97-6833-4f57-86f2-962de9fe2d82

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
theorem _root_.solution (X : Matrix (Fin g) (Fin g) ℝ) : IsUnit (unip X) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  simp [unip]
end GroundTheory.Heights₂.Heights.KCoord
