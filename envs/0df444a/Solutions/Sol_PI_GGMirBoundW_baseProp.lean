-- Prove2me | solution 1 for PI.GGMirBoundW.baseProp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:59:48.659838+00:00
-- url     : https://prove2.me/submissions/a900cfd5-c8d9-4aa1-81ac-f034b7d9f7b7

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
theorem _root_.solution : BaseProp := by
  intro F _ _ ψ₀ _ V _ _ π ℓ hℓ _
  have hD : D F (0 + 1) = 1 := by simp [D]
  show ∃ p : Fin (D F (0 + 1)) → GL (Fin (0 + 1)) F, _
  rw [hD]
  refine ⟨fun _ => 1, fun _ j => ?_, ?_⟩
  · simp only [Units.val_one]
    rw [Matrix.one_apply]
    exact if_congr eq_comm rfl rfl
  · rw [linearIndependent_unique_iff]
    show ℓ ∘ₗ π 1 ≠ 0
    rw [map_one]
    intro h
    apply hℓ
    ext v
    simpa using LinearMap.congr_fun h v
end PI.GGMirBoundW
