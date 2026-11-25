-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GraphJacContinuous_proof_b323438eeb5d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:44:22.425094+00:00
-- url     : https://prove2.me/submissions/7e895f4e-21fe-483e-a55d-a5bd5a407d98

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGraphJacContinuous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGraphJacContinuous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_graphJac_pos_8f8be9a41ec1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_continuous_graphJac_e29ede2893b7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
noncomputable section
open scoped InnerProductSpace
namespace GroundTheory.Heights₂.Heights
namespace GraphJacContinuous
theorem _root_.solution : GraphJacContinuous.Statement := by
  intro k m A ε hε
  set g := fun B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m) =>
    graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) with hg
  have hgA : 0 < g A := graphJac_pos _
  set η := ε * g A / (1 + ε) with hη
  have hη0 : 0 < η := by positivity
  have hηe : (1 + ε) * η = ε * g A := by rw [hη]; field_simp
  obtain ⟨δ, hδ, hδη⟩ := Metric.continuous_iff.mp (continuous_graphJac k m) A η hη0
  refine ⟨δ / 2, half_pos hδ, fun B hB => ?_⟩
  have hd : dist B A < δ := by rw [dist_eq_norm]; linarith
  have h := hδη B hd
  rw [Real.dist_eq, abs_lt] at h
  change g B ≤ (1 + ε) * g A ∧ g A ≤ (1 + ε) * g B
  constructor
  · nlinarith
  · nlinarith
end GraphJacContinuous
end GroundTheory.Heights₂.Heights
