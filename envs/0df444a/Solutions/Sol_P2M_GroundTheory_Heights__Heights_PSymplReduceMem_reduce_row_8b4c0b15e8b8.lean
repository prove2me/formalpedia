-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplReduceMem_reduce_row_8b4c0b15e8b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:46:14.097631+00:00
-- url     : https://prove2.me/submissions/90b16fa8-58bc-4fa4-b4b9-622ac16f940c

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
theorem _root_.solution {n : ℕ} (H : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ)
    (a : Fin n ⊕ Fin n) :
    symplReduce H a = symplTail (H (Sum.map Fin.succ Fin.succ a)) -
      (H (Sum.map Fin.succ Fin.succ a) (Sum.inl 0) / H (Sum.inl 0) (Sum.inl 0)) •
        symplTail (H (Sum.inl 0)) := by
  funext b
  simp only [symplReduce, symplTail, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
end GroundTheory.Heights₂.Heights.PSymplReduceMem
