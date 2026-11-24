-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InjectiveHolomorphicOpen_hypotheses_inhabited_12237f493c3a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:03.978263+00:00
-- url     : https://prove2.me/submissions/227ededf-d402-4126-bf43-65a4e89e58d9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInjectiveHolomorphicOpen

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
namespace InjectiveHolomorphicOpen
theorem _root_.solution :
    IsOpen (Metric.ball (0 : Fin 2 → ℂ) 1) ∧
      DifferentiableOn ℂ (fun t : Fin 2 → ℂ => ![t 0, t 1 + t 0 ^ 2]) (Metric.ball 0 1) ∧
      Set.InjOn (fun t : Fin 2 → ℂ => ![t 0, t 1 + t 0 ^ 2]) (Metric.ball 0 1) := by
  refine ⟨Metric.isOpen_ball, ?_, ?_⟩
  · refine Differentiable.differentiableOn ?_
    rw [differentiable_pi]
    intro i
    fin_cases i
    · simpa using differentiable_apply (𝕜 := ℂ) (0 : Fin 2)
    · have hd : Differentiable ℂ (fun x : Fin 2 → ℂ => x 1 + x 0 ^ 2) := by fun_prop
      exact hd
  · intro s _ t _ hst
    have h0 : s 0 = t 0 := by simpa using congrFun hst 0
    have h1 : s 1 + s 0 ^ 2 = t 1 + t 0 ^ 2 := by simpa using congrFun hst 1
    funext i
    fin_cases i
    · exact h0
    · simp only [Fin.mk_one]
      rw [h0] at h1
      exact add_right_cancel h1
end InjectiveHolomorphicOpen
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
