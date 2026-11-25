-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.cca_hasFDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:14:26.360968+00:00
-- url     : https://prove2.me/submissions/b2f3f775-25f5-4bf4-b7cb-e315face570e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_cca_cont_theta
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_cca_bounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric Set Filter Topology MeasureTheory Complex
open scoped ContDiff Real
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution [FiniteDimensional ℂ X] {F : X → E} {U : Set X} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) (hD : ContinuousOn (fderiv ℂ F) U) {κ a : ℝ → ℂ}
    (hκ : Continuous κ) (ha : Continuous a) {z₀ u : X} {δ : ℝ} (hδ : 0 < δ)
    (hsub : ∀ z ∈ closedBall z₀ δ, ∀ θ, z + a θ • u ∈ U) :
    HasFDerivAt (fun z => ∫ θ in (0 : ℝ)..2 * π, κ θ • F (z + a θ • u))
      (∫ θ in (0 : ℝ)..2 * π, κ θ • fderiv ℂ F (z₀ + a θ • u)) z₀ := by
  obtain ⟨B, hB⟩ := cca_bounds hD hκ ha hsub
  have hball : closedBall z₀ δ ∈ 𝓝 z₀ := closedBall_mem_nhds z₀ hδ
  have hd : ∀ z ∈ closedBall z₀ δ, ∀ θ, HasFDerivAt (fun x => κ θ • F (x + a θ • u))
      (κ θ • fderiv ℂ F (z + a θ • u)) z := by
    intro z hz θ
    have h1 : HasFDerivAt F (fderiv ℂ F (z + a θ • u)) (z + a θ • u) :=
      (hF.differentiableAt (hU.mem_nhds (hsub z hz θ))).hasFDerivAt
    have h2 := h1.comp z ((hasFDerivAt_id z).add_const (a θ • u))
    have h3 := h2.const_smul (κ θ)
    simp only [ContinuousLinearMap.comp_id] at h3
    exact h3
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ)
    (F' := fun z θ => κ θ • fderiv ℂ F (z + a θ • u)) (bound := fun _ => B)
    hball ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hball] with z hz
    exact (cca_cont_theta hF.continuousOn hκ ha (hsub z hz)).aestronglyMeasurable
  · exact (cca_cont_theta hF.continuousOn hκ ha
      (hsub z₀ (mem_closedBall_self hδ.le))).intervalIntegrable _ _
  · exact (cca_cont_theta hD hκ ha (hsub z₀ (mem_closedBall_self hδ.le))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun θ hθ z hz => hB z hz θ hθ)
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall (fun θ _ z hz => hd z hz θ)
end ReciprocityTheory.ChartRestriction.DS.S7
