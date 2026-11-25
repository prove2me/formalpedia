-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplReduceMem_J_succ_e_dec9e46caacf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:46:19.829678+00:00
-- url     : https://prove2.me/submissions/a64ad5a4-addd-4e49-b7db-3cb7bd83cdda

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
theorem _root_.solution {n : ℕ} (a : Fin n ⊕ Fin n) :
    J (Fin (n + 1)) ℝ (Sum.map Fin.succ Fin.succ a) (Sum.inl 0) = 0 := by
  rcases a with i | i <;> simp [J, one_apply, Fin.succ_ne_zero]
end GroundTheory.Heights₂.Heights.PSymplReduceMem
