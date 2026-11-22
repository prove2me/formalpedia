-- Prove2me | solution 1 for PI.GGMirBoundW.colM_lc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:16.460809+00:00
-- url     : https://prove2.me/submissions/b4d2ba7c-725d-4c4a-9bfe-2a8d7fbb2f16

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_LastRowMul
import Theorems.Thm_PI_GGMirBoundW_blkM_cc
import Theorems.Thm_PI_GGMirBoundW_blkM_cl
import Theorems.Thm_PI_GGMirBoundW_blkM_lc
import Theorems.Thm_PI_GGMirBoundW_blkM_ll
import Theorems.Thm_PI_GGMirBoundW_colM_cc
import Theorems.Thm_PI_GGMirBoundW_colM_cl
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
attribute [local simp] PI.GGMirBoundW.colM_cc
attribute [local simp] PI.GGMirBoundW.colM_cl

set_option autoImplicit false
open PI PI.GGMirBoundW
open Matrix Formalism.L2.SG.GGMirabolic
noncomputable section
open Classical
variable {F : Type} [Field F] [Fintype F] {n : ℕ}
namespace PI.GGMirBoundW
theorem _root_.solution (x : Fin n → F) (j : Fin n) :
    colM x (Fin.last n) (Fin.castSucc j) = 0 := by
  simp [colM, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]
end PI.GGMirBoundW
