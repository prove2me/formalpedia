-- Prove2me | solution 1 for PI.GGMirBoundW.conjCol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:40:48.046155+00:00
-- url     : https://prove2.me/submissions/cf892a21-3dd2-43d1-b09d-0a60487aa713

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_LastRowMul
import Theorems.Thm_PI_GGMirBoundW_blkM_cc
import Theorems.Thm_PI_GGMirBoundW_blkM_cl
import Theorems.Thm_PI_GGMirBoundW_blkM_lc
import Theorems.Thm_PI_GGMirBoundW_blkM_ll
import Theorems.Thm_PI_GGMirBoundW_colM_cc
import Theorems.Thm_PI_GGMirBoundW_colM_cl
import Theorems.Thm_PI_GGMirBoundW_colM_lc
import Theorems.Thm_PI_GGMirBoundW_colM_ll
import Theorems.Thm_PI_GGMirBoundW_E_val
import Theorems.Thm_PI_GGMirBoundW_col_val
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
attribute [local simp] PI.GGMirBoundW.colM_lc
attribute [local simp] PI.GGMirBoundW.colM_ll

set_option autoImplicit false
open PI PI.GGMirBoundW
open Matrix Formalism.L2.SG.GGMirabolic
noncomputable section
open Classical
namespace PI.GGMirBoundW
theorem _root_.solution : ConjCol := by
  intro F _ _ n A x
  ext : 1
  simp only [Units.val_mul, E_val, col_val, blkM, colM]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  congr 2
  · simp
  · ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · simp
  · simp
end PI.GGMirBoundW
