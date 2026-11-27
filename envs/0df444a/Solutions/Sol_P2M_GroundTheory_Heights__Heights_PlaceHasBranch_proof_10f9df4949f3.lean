-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PlaceHasBranch_proof_10f9df4949f3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:06:49.869036+00:00
-- url     : https://prove2.me/submissions/832c7e7b-a578-4ded-902a-2dfd5ab914d0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPlaceHasBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPlaceBranchExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedBranchInOneBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedBranchSameOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPlaceHasBranch

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
open MvPolynomial ComplexSets Filter Topology
namespace GroundTheory.Heights₂.Heights
namespace PlaceHasBranch
theorem _root_.solution (h₁ : PlaceBranchExists.Statement) (h₂ : PuncturedBranchInOneBranch.Statement)
    (h₃ : PuncturedBranchSameOrder.Statement) : PlaceHasBranch.Statement := by
  intro n I q m c hrad hdim hcov hdisj P
  obtain ⟨N, hN, hNc⟩ := hcov
  obtain ⟨ν, hν⟩ := h₁ n I q hrad hdim P
  have hnorm : ∀ τ : ℂ, ‖(fun _ ↦ τ : Fin 1 → ℂ)‖ = ‖τ‖ := fun τ ↦ by simp [pi_norm_const]

  have hcont : ContinuousAt (fun τ : ℂ ↦ ν.toFun (fun _ ↦ τ)) 0 := by
    have h0 : ContinuousAt ν.toFun (fun _ ↦ (0 : ℂ)) :=
      ν.differentiableOn.continuousOn.continuousAt
        (Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_zero_right, hnorm] using ν.radius_pos))
    exact h0.comp (continuous_pi fun _ ↦ continuous_id).continuousAt
  have hq : ν.toFun (fun _ ↦ (0 : ℂ)) = q := ν.map_zero
  have hev : ∀ᶠ τ in 𝓝 (0 : ℂ), ν.toFun (fun _ ↦ τ) ∈ N := hcont.preimage_mem_nhds (by rw [hq]; exact hN)
  obtain ⟨ε, hε, hεN⟩ := Metric.eventually_nhds_iff.1 hev

  have hin : ∀ τ : ℂ, 0 < ‖τ‖ → ‖τ‖ < min ε ν.radius → ν.toFun (fun _ ↦ τ) ∈ ⋃ b, (c b).image := by
    intro τ _ hτ
    refine hNc ⟨ν.mapsTo ?_, hεN ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, hnorm]
      exact hτ.trans_le (min_le_right _ _)
    · rw [dist_zero_right]
      exact hτ.trans_le (min_le_left _ _)
  obtain ⟨b, ρ', hρ', hb⟩ := h₂ n I q m c ν (min ε ν.radius) hrad hdim (lt_min hε ν.radius_pos) hin hdisj
  exact ⟨b, fun f ↦ (hν f).trans (h₃ n I q (c b) ν ρ' hrad hdim hρ' hb f).symm⟩
end PlaceHasBranch
end GroundTheory.Heights₂.Heights
