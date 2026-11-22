-- Prove2me | solution 1 for PI.GGMirBoundW.blkM_cl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:03:17.142537+00:00
-- url     : https://prove2.me/submissions/41c52136-9cb2-479d-8ae2-b582e79119ae

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_LastRowMul
import Theorems.Thm_PI_GGMirBoundW_blkM_cc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.GGMirBoundW.blkM_cc

set_option autoImplicit false
open PI PI.GGMirBoundW
open Matrix Formalism.L2.SG.GGMirabolic
noncomputable section
open Classical
variable {F : Type} [Field F] [Fintype F] {n : ℕ}
namespace PI.GGMirBoundW
theorem _root_.solution (A : Matrix (Fin n) (Fin n) F) (i : Fin n) :
    blkM A (Fin.castSucc i) (Fin.last n) = 0 := by
  simp [blkM, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]
end PI.GGMirBoundW
