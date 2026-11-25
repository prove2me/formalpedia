-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplExtMem_row_e_6d67875bd178
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:46:04.822668+00:00
-- url     : https://prove2.me/submissions/f8aefe4d-62ab-42b4-b4bf-6d6bc566c812

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
theorem _root_.solution : symplExt α β γ δ Q (Sum.inl 0) = symplCons α β 0 := rfl
end GroundTheory.Heights₂.Heights.PSymplExtMem
