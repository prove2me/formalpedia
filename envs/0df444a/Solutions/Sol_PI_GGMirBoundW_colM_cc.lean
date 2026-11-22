-- Prove2me | solution 1 for PI.GGMirBoundW.colM_cc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:05.661825+00:00
-- url     : https://prove2.me/submissions/2f00ee61-0159-4c1c-8f47-34180d0df272

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_LastRowMul
import Theorems.Thm_PI_GGMirBoundW_blkM_cc
import Theorems.Thm_PI_GGMirBoundW_blkM_cl
import Theorems.Thm_PI_GGMirBoundW_blkM_lc
import Theorems.Thm_PI_GGMirBoundW_blkM_ll
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
attribute [local simp] PI.GGMirBoundW.blkM_ll

set_option autoImplicit false
open PI PI.GGMirBoundW
open Matrix Formalism.L2.SG.GGMirabolic
noncomputable section
open Classical
variable {F : Type} [Field F] [Fintype F] {n : ℕ}
namespace PI.GGMirBoundW
theorem _root_.solution (x : Fin n → F) (i j : Fin n) :
    colM x (Fin.castSucc i) (Fin.castSucc j) = (1 : Matrix (Fin n) (Fin n) F) i j := by
  simp [colM, finSumFinEquiv_symm_apply_castSucc]
end PI.GGMirBoundW
