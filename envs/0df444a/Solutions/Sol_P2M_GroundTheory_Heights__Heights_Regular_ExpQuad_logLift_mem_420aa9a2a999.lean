-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_logLift_mem_420aa9a2a999
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:49:02.488806+00:00
-- url     : https://prove2.me/submissions/5208899c-e4bd-47e6-a7f6-ad32c7443f49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StPuncturedExpOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PExpExtension
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_norm_lt_one_of_mem_ball_6be07bfbd056
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_logLift_castLE_f986c713271f

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
theorem _root_.solution {z : Fin n → ℂ} (hz : z ∈ puncturedChart P.a_le (ball 0 1)) :
    logLift a z ∈ logCover P.a_le := by
  refine ⟨fun i => ?_, fun k hk => ?_⟩
  · rw [logLift_castLE P, Complex.log_re]
    have h0 : z (Fin.castLE P.a_le i) ≠ 0 := hz.2 i
    exact Real.log_neg (norm_pos_iff.mpr h0) (norm_lt_one_of_mem_ball hz.1 _)
  · have : ¬ k.val < a := not_lt.mpr hk
    simp only [logLift, this, if_false]
    exact norm_lt_one_of_mem_ball hz.1 k
end GroundTheory.Heights₂.Heights.Regular.ExpQuad
