-- Prove2me | solution 1 for PI.GGMirBoundW.colM_cl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:16:28.732861+00:00
-- url     : https://prove2.me/submissions/f39c1e7b-2afb-451e-9acd-42a05e28b236

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_LastRowMul
import Theorems.Thm_PI_GGMirBoundW_blkM_cc
import Theorems.Thm_PI_GGMirBoundW_blkM_cl
import Theorems.Thm_PI_GGMirBoundW_blkM_lc
import Theorems.Thm_PI_GGMirBoundW_blkM_ll
import Theorems.Thm_PI_GGMirBoundW_colM_cc
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

set_option autoImplicit false
open PI PI.GGMirBoundW
open Matrix Formalism.L2.SG.GGMirabolic
noncomputable section
open Classical
variable {F : Type} [Field F] [Fintype F] {n : ℕ}
namespace PI.GGMirBoundW
theorem _root_.solution (x : Fin n → F) (i : Fin n) :
    colM x (Fin.castSucc i) (Fin.last n) = x i := by
  simp [colM, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]
end PI.GGMirBoundW
