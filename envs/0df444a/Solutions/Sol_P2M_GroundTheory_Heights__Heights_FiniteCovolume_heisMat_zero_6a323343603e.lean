-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_zero_6a323343603e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:54:35.527958+00:00
-- url     : https://prove2.me/submissions/de751f5e-918d-448b-ac5a-ebfd11140741

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
variable [DecidableEq ι]
variable {H : Matrix ι ι ℂ} {a : ι → ℂ}
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution : heisMat H a 0 0 = 1 := by
  simp [heisMat]
end GroundTheory.Heights₂.Heights.FiniteCovolume
