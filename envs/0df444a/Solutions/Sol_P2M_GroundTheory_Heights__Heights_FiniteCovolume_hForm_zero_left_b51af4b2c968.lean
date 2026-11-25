-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_zero_left_b51af4b2c968
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:54:14.43698+00:00
-- url     : https://prove2.me/submissions/6158c997-f124-42ef-b8cf-66a95aeca8ac

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
variable (H : Matrix ι ι ℂ)
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution (z : ι → ℂ) : hForm H 0 z = 0 := by simp [hForm]
end GroundTheory.Heights₂.Heights.FiniteCovolume
