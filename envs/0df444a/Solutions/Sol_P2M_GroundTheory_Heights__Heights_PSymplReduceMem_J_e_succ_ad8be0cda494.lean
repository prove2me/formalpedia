-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplReduceMem_J_e_succ_ad8be0cda494
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:46:18.383297+00:00
-- url     : https://prove2.me/submissions/b13fb0ec-6f84-4445-ba83-24a06cf9c139

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplReduceMem

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
open GroundTheory.Heights₂.Heights.PSymplReduceMem
namespace GroundTheory.Heights₂.Heights.PSymplReduceMem
theorem _root_.solution {n : ℕ} (b : Fin n ⊕ Fin n) :
    J (Fin (n + 1)) ℝ (Sum.inl 0) (Sum.map Fin.succ Fin.succ b) = 0 := by
  rcases b with j | j <;> simp [J, one_apply, (Fin.succ_ne_zero j).symm]
end GroundTheory.Heights₂.Heights.PSymplReduceMem
