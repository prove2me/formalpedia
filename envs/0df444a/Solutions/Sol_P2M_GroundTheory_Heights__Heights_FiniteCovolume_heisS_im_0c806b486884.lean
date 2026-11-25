-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisS_im_0c806b486884
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:54:40.553207+00:00
-- url     : https://prove2.me/submissions/20489809-183c-44f9-9fd1-fe40e3085af8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι]
variable {H : Matrix ι ι ℂ}
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution (y : ι → ℂ) (t : ℝ) : (heisS H y t).im = t := rfl
end GroundTheory.Heights₂.Heights.FiniteCovolume
