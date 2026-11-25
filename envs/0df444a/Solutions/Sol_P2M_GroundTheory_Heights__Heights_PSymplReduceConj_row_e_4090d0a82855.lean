-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplReduceConj_row_e_4090d0a82855
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:46:16.267953+00:00
-- url     : https://prove2.me/submissions/0fd2c43a-52f5-4bf2-9bf9-658907a16690

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplReduceConj

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
open GroundTheory.Heights₂.Heights.PSymplReduceConj
namespace GroundTheory.Heights₂.Heights.PSymplReduceConj
theorem _root_.solution {n : ℕ} (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    symplExt (1 : ℝ) 0 0 1 Q (Sum.inl 0) = symplCons 1 0 0 :=
  rfl
end GroundTheory.Heights₂.Heights.PSymplReduceConj
