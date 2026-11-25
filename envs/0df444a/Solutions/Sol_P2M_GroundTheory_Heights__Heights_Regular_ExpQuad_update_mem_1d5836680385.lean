-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_update_mem_1d5836680385
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:48:53.015887+00:00
-- url     : https://prove2.me/submissions/f9d3def6-1905-44d4-87f8-10ee1f642f70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StPuncturedExpOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PExpExtension
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_cusp_ne_10e65f158bd3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_norm_lt_one_of_mem_ball_6be07bfbd056
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_mem_ball_of_forall_d3fc66dee939

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
theorem _root_.solution {z : Fin n → ℂ} (hz : z ∈ ball (0 : Fin n → ℂ) 1) (i : Fin a)
    (hne : ∀ j : Fin a, j ≠ i → z (Fin.castLE P.a_le j) ≠ 0) {x : ℂ}
    (hx : x ∈ ball (0 : ℂ) 1 \ {0}) :
    Function.update z (Fin.castLE P.a_le i) x ∈ puncturedChart P.a_le (ball 0 1) := by
  classical
  refine ⟨mem_ball_of_forall fun k => ?_, fun j => ?_⟩
  · by_cases hk : k = Fin.castLE P.a_le i
    · subst hk
      simp only [Function.update_self]
      simpa using hx.1
    · rw [Function.update_of_ne hk]
      exact norm_lt_one_of_mem_ball hz k
  · show Function.update z (Fin.castLE P.a_le i) x (Fin.castLE P.a_le j) ≠ 0
    by_cases hj : j = i
    · subst hj
      simp only [Function.update_self]
      exact hx.2
    · rw [Function.update_of_ne (cusp_ne P hj)]
      exact hne j hj
end GroundTheory.Heights₂.Heights.Regular.ExpQuad
