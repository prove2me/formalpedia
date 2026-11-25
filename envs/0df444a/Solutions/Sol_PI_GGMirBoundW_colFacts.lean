-- Prove2me | solution 1 for PI.GGMirBoundW.colFacts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:40:45.138786+00:00
-- url     : https://prove2.me/submissions/4b4062c0-f776-4668-adb3-ae71db413c1d

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
theorem _root_.solution : ColFacts := by
  intro F _ _ n x
  refine ⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩
  · rw [col_val]
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simp
  · rw [col_val]
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd hij (lt_irrefl _)
      | cast j => simp
    | cast i =>
      induction j using Fin.lastCases with
      | last => exact absurd hij (not_lt.mpr (Fin.castSucc_lt_last i).le)
      | cast j =>
        simp only [colM_cc]
        exact Matrix.one_apply_ne (ne_of_gt (Fin.castSucc_lt_castSucc_iff.mp hij))
  · rw [col_val]
    unfold superdiag
    have h0 : ∀ i j : Fin (n + 1),
        (if (j : ℕ) = (i : ℕ) + 1 then (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) i j else 0) = 0 := by
      intro i j
      split_ifs with h
      · rw [Matrix.one_apply_ne]
        intro e; subst e; omega
      · rfl
    have hl : ∀ i : Fin (n + 1), (n = (i : ℕ)) ↔ (i = Fin.last n) := by
      intro i; rw [Fin.ext_iff, Fin.val_last]; omega
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.sum_univ_castSucc (n := n + 1), colM_cc, colM_cl, colM_lc, colM_ll, Fin.val_castSucc,
      Fin.val_last, h0, ite_self, add_left_inj, hl]
    simp
end PI.GGMirBoundW
