-- Prove2me | solution 1 for PI.GGMirBoundW.blkFacts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:42:31.541091+00:00
-- url     : https://prove2.me/submissions/6630717a-6934-459d-86e1-b3b0ffe0207c

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
theorem _root_.solution : UnitriangularBlockExtension := by
  intro F _ _ n u hu
  obtain ⟨hd, hl⟩ := hu
  refine ⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩
  · rw [E_val]
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simpa using hd i
  · rw [E_val]
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd hij (lt_irrefl _)
      | cast j => simp
    | cast i =>
      induction j using Fin.lastCases with
      | last => exact absurd hij (not_lt.mpr (Fin.castSucc_lt_last i).le)
      | cast j =>
        simp only [blkM_cc]
        exact hl i j (Fin.castSucc_lt_castSucc_iff.mp hij)
  · rw [E_val]
    unfold superdiag
    simp [Fin.sum_univ_castSucc]
end PI.GGMirBoundW
