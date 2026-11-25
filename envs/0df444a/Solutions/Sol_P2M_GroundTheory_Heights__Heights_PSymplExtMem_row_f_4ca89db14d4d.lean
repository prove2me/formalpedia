-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplExtMem_row_f_4ca89db14d4d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:46:07.320448+00:00
-- url     : https://prove2.me/submissions/ab56c588-f2e9-41c3-9f5d-a4f66bd51cae

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
theorem _root_.solution : symplExt α β γ δ Q (Sum.inr 0) = symplCons γ δ 0 := rfl
end GroundTheory.Heights₂.Heights.PSymplExtMem
