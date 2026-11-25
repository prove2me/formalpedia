-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_neg_right_013bd065af05
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:54:35.851786+00:00
-- url     : https://prove2.me/submissions/6729dc5f-ee2f-4369-a166-2f92a0038e4c

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
theorem _root_.solution (u z : ι → ℂ) : hForm H u (-z) = -hForm H u z := by
  simp [hForm, mulVec_neg, dotProduct_neg]
end GroundTheory.Heights₂.Heights.FiniteCovolume
