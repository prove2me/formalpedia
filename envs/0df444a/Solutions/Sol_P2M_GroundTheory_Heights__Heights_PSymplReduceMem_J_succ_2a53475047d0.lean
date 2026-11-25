-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplReduceMem_J_succ_2a53475047d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:46:19.168341+00:00
-- url     : https://prove2.me/submissions/377ea443-4a9d-415d-a23f-7bb1e96bb7c3

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
theorem _root_.solution {n : ℕ} (a b : Fin n ⊕ Fin n) :
    J (Fin (n + 1)) ℝ (Sum.map Fin.succ Fin.succ a) (Sum.map Fin.succ Fin.succ b) =
      J (Fin n) ℝ a b := by
  rcases a with i | i <;> rcases b with j | j <;> simp [J, one_apply, Fin.succ_inj]
end GroundTheory.Heights₂.Heights.PSymplReduceMem
