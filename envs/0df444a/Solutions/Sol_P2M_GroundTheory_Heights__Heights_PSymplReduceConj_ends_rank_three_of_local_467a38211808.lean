-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplReduceConj_ends_rank_three_of_local_467a38211808
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:46:12.075341+00:00
-- url     : https://prove2.me/submissions/8d2d2345-fbd5-4c05-9424-5edf83f38990

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
theorem _root_.solution {n : ℕ} (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (a : Fin n ⊕ Fin n) :
    symplExt (1 : ℝ) 0 0 1 Q (Sum.map Fin.succ Fin.succ a) = symplCons 0 0 (Q a) := by
  cases a <;> rfl
end GroundTheory.Heights₂.Heights.PSymplReduceConj
