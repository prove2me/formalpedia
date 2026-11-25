-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_slice_noncusp_f59f6f6ffc67
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:49:26.761029+00:00
-- url     : https://prove2.me/submissions/d4c6d432-73ce-4c3b-a931-2291b0c66ee2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StPuncturedExpOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PExpExtension
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
theorem _root_.solution {F : (Fin n → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (puncturedChart P.a_le (ball 0 1)))
    {z : Fin n → ℂ} (hz : z ∈ ball (0 : Fin n → ℂ) 1) (m : Fin n) (hm : ¬ m.val < a)
    (hne : ∀ j, j ≠ m → z j ≠ 0) :
    ∃ c : ℂ, Tendsto (fun x => F (Function.update z m x)) (𝓝[≠] 0) (𝓝 c) := by
  classical
  have hmem : Function.update z m 0 ∈ puncturedChart P.a_le (ball 0 1) := by
    refine ⟨mem_ball_of_forall fun k => ?_, fun j => ?_⟩
    · by_cases hk : k = m
      · subst hk
        simp
      · rw [Function.update_of_ne hk]
        exact norm_lt_one_of_mem_ball hz k
    · have hjm : Fin.castLE P.a_le j ≠ m := by
        intro e
        apply hm
        rw [← e, Fin.val_castLE]
        exact j.isLt
      show Function.update z m 0 (Fin.castLE P.a_le j) ≠ 0
      rw [Function.update_of_ne hjm]
      exact hne _ hjm
  refine ⟨F (Function.update z m 0), ?_⟩
  have hc : Continuous (fun x : ℂ => Function.update z m x) :=
    (continuous_const (y := z)).update m (continuous_id (X := ℂ))
  exact ((hF _ hmem).continuousAt.tendsto.comp (hc.tendsto 0)).mono_left nhdsWithin_le_nhds
end GroundTheory.Heights₂.Heights.Regular.ExpQuad
