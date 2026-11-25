-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_eq_of_continuousAt_e738391b5387
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:53:50.688439+00:00
-- url     : https://prove2.me/submissions/11d32332-9bf3-40e4-b3b3-2a5f6f097fde

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StPuncturedExpOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PExpExtension

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
namespace GroundTheory.Heights₂.Heights.Regular.ExpQuad
theorem _root_.solution {n : ℕ} {F₁ F₂ : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hz : z ∈ ball (0 : Fin n → ℂ) 1) (h₁ : ContinuousAt F₁ z) (h₂ : ContinuousAt F₂ z)
    (heq : ∀ y ∈ ball (0 : Fin n → ℂ) 1, (∀ i, y i ≠ 0) → F₁ y = F₂ y) : F₁ z = F₂ z := by
  let γ : ℝ → Fin n → ℂ := fun t k => z k + (t : ℂ)
  have hγc : Continuous γ := by
    refine continuous_pi fun k => ?_
    exact continuous_const.add Complex.continuous_ofReal
  have hγ0 : γ 0 = z := by funext k; simp [γ]
  have hγ : Tendsto γ (𝓝[>] 0) (𝓝 z) := by
    rw [← hγ0]
    exact (hγc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hball : ∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ∈ ball (0 : Fin n → ℂ) 1 :=
    hγ.eventually (isOpen_ball.mem_nhds hz)
  have hne : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ k, γ t k ≠ 0 := by
    rw [Filter.eventually_all]
    intro k
    by_cases hk : z k = 0
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [γ, hk, zero_add, ne_eq, Complex.ofReal_eq_zero]
      exact ne_of_gt ht
    · exact (((continuous_apply k).tendsto z).comp hγ).eventually_ne hk
  have e₁ : Tendsto (F₁ ∘ γ) (𝓝[>] 0) (𝓝 (F₁ z)) := h₁.tendsto.comp hγ
  have e₂ : Tendsto (F₂ ∘ γ) (𝓝[>] 0) (𝓝 (F₂ z)) := h₂.tendsto.comp hγ
  have e₁' : Tendsto (F₂ ∘ γ) (𝓝[>] 0) (𝓝 (F₁ z)) := by
    refine e₁.congr' ?_
    filter_upwards [hball, hne] with t h1 h2
    exact heq _ h1 h2
  exact tendsto_nhds_unique e₁' e₂
end GroundTheory.Heights₂.Heights.Regular.ExpQuad
