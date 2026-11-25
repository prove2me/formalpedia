-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_expCover_mem_bb0f4093b319
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:49:00.487422+00:00
-- url     : https://prove2.me/submissions/ff5bb4df-72a0-4c9b-87ae-178a4ae559f6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StPuncturedExpOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PExpExtension
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_mem_ball_of_forall_d3fc66dee939
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_expCover_castLE_214aca7e295d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.ExpQuad
variable {n a g : ℕ} (P : PeriodPolydisc n a g) (v : Fin g → ℤ)
namespace GroundTheory.Heights₂.Heights.Regular.ExpQuad
theorem _root_.solution {w : Fin n → ℂ} (hw : w ∈ logCover P.a_le) :
    expCover a w ∈ puncturedChart P.a_le (ball 0 1) := by
  refine ⟨mem_ball_of_forall fun k => ?_, fun j => ?_⟩
  · by_cases hk : k.val < a
    · have hk' : Fin.castLE P.a_le ⟨k.val, hk⟩ = k := Fin.ext rfl
      have h1 := hw.1 ⟨k.val, hk⟩
      rw [hk'] at h1
      simp only [expCover, hk, if_true, Complex.norm_exp]
      exact (Real.exp_lt_exp.mpr h1).trans_eq Real.exp_zero
    · simp only [expCover, hk, if_false]
      exact hw.2 k (not_lt.mp hk)
  · show expCover a w (Fin.castLE P.a_le j) ≠ 0
    rw [expCover_castLE P]
    exact Complex.exp_ne_zero _
end GroundTheory.Heights₂.Heights.Regular.ExpQuad
