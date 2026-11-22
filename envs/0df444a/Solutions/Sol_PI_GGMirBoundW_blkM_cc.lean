-- Prove2me | solution 1 for PI.GGMirBoundW.blkM_cc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:59:45.912728+00:00
-- url     : https://prove2.me/submissions/33c3c006-9417-453a-8b95-b92c1c93ab3e

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
theorem _root_.solution (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    blkM A (Fin.castSucc i) (Fin.castSucc j) = A i j := by
  simp [blkM, finSumFinEquiv_symm_apply_castSucc]
end PI.GGMirBoundW
