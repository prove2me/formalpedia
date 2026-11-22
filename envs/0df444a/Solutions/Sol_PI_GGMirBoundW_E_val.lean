-- Prove2me | solution 1 for PI.GGMirBoundW.E_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:16.909245+00:00
-- url     : https://prove2.me/submissions/46d559b3-3b0e-43db-b2ea-0dfd2802eb05

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_LastRowMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.GGMirBoundW
open Matrix Formalism.L2.SG.GGMirabolic
noncomputable section
open Classical
variable {F : Type} [Field F] [Fintype F] {n : ℕ}
namespace PI.GGMirBoundW
theorem _root_.solution (A : GL (Fin n) F) : ((E F n A : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) =
    blkM (A : Matrix (Fin n) (Fin n) F) := rfl
end PI.GGMirBoundW
