-- Prove2me | solution 1 for PI.GGMirBoundW.blkM_ll
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:09:06.733806+00:00
-- url     : https://prove2.me/submissions/444174eb-4af0-44d7-9438-909df3158458

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_LastRowMul
import Theorems.Thm_PI_GGMirBoundW_blkM_cc
import Theorems.Thm_PI_GGMirBoundW_blkM_cl
import Theorems.Thm_PI_GGMirBoundW_blkM_lc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.GGMirBoundW.blkM_cc
attribute [local simp] PI.GGMirBoundW.blkM_cl
attribute [local simp] PI.GGMirBoundW.blkM_lc

set_option autoImplicit false
open PI PI.GGMirBoundW
open Matrix Formalism.L2.SG.GGMirabolic
noncomputable section
open Classical
variable {F : Type} [Field F] [Fintype F] {n : ℕ}
namespace PI.GGMirBoundW
theorem _root_.solution (A : Matrix (Fin n) (Fin n) F) :
    blkM A (Fin.last n) (Fin.last n) = 1 := by
  simp [blkM, finSumFinEquiv_symm_last]
end PI.GGMirBoundW
