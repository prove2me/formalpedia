-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InvarianceOfDomain_hypotheses_inhabited_1e901b271c70
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:58:35.70283+00:00
-- url     : https://prove2.me/submissions/78762b19-a66f-4945-b121-3e6d7fcef531

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInvarianceOfDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace InvarianceOfDomain
theorem _root_.solution :
    IsOpen (Metric.ball (0 : Fin 2 → ℝ) 1) ∧
      ContinuousOn (fun x : Fin 2 → ℝ => ![x 0, x 1 + x 0 ^ 3]) (Metric.ball 0 1) ∧
      Set.InjOn (fun x : Fin 2 → ℝ => ![x 0, x 1 + x 0 ^ 3]) (Metric.ball 0 1) := by
  refine ⟨Metric.isOpen_ball, ?_, ?_⟩
  · refine Continuous.continuousOn ?_
    refine continuous_pi fun i => ?_
    fin_cases i
    · simpa using continuous_apply (0 : Fin 2)
    · have hc : Continuous (fun x : Fin 2 → ℝ => x 1 + x 0 ^ 3) := by fun_prop
      exact hc
  · intro s _ t _ hst
    have h0 : s 0 = t 0 := by simpa using congrFun hst 0
    have h1 : s 1 + s 0 ^ 3 = t 1 + t 0 ^ 3 := by simpa using congrFun hst 1
    funext i
    fin_cases i
    · exact h0
    · simp only [Fin.mk_one]
      rw [h0] at h1
      exact add_right_cancel h1
end InvarianceOfDomain
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
