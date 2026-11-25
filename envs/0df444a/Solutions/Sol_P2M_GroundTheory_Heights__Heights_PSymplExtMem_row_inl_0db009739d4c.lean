-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplExtMem_row_inl_0db009739d4c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:46:08.407607+00:00
-- url     : https://prove2.me/submissions/5da4fb76-9e5b-48a2-8d7b-38822815d422

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplExtMem

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
open GroundTheory.Heights₂.Heights.PSymplExtMem
variable {R : Type*} [Zero R] {n : ℕ} (α β γ δ : R) (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
namespace GroundTheory.Heights₂.Heights.PSymplExtMem
theorem _root_.solution (i : Fin n) :
    symplExt α β γ δ Q (Sum.inl i.succ) = symplCons 0 0 (Q (Sum.inl i)) := rfl
end GroundTheory.Heights₂.Heights.PSymplExtMem
