-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplExtMem_row_inr_f2f09600dc08
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:46:09.47102+00:00
-- url     : https://prove2.me/submissions/bf36e222-88f9-4a71-8b12-f41e49eba471

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
    symplExt α β γ δ Q (Sum.inr i.succ) = symplCons 0 0 (Q (Sum.inr i)) := rfl
end GroundTheory.Heights₂.Heights.PSymplExtMem
