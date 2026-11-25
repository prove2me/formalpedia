-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.cca_contAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:14:20.457797+00:00
-- url     : https://prove2.me/submissions/7e4944d5-773a-4770-841a-553b231d038b

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
    (hF : ContinuousOn F U) {κ a : ℝ → ℂ} (hκ : Continuous κ) (ha : Continuous a) {z₀ u : X}
    {δ : ℝ} (hδ : 0 < δ) (hsub : ∀ z ∈ closedBall z₀ δ, ∀ θ, z + a θ • u ∈ U) :
    ContinuousAt (fun z => ∫ θ in (0 : ℝ)..2 * π, κ θ • F (z + a θ • u)) z₀ := by
  obtain ⟨B, hB⟩ := cca_bounds hF hκ ha hsub
  have hball : closedBall z₀ δ ∈ 𝓝 z₀ := closedBall_mem_nhds z₀ hδ
  apply intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => B)
  · filter_upwards [hball] with z hz
    exact (cca_cont_theta hF hκ ha (hsub z hz)).aestronglyMeasurable
  · filter_upwards [hball] with z hz
    exact Filter.Eventually.of_forall (fun θ hθ => hB z hz θ hθ)
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall (fun θ _ => ?_)
    have hmem : z₀ + a θ • u ∈ U := hsub z₀ (mem_closedBall_self hδ.le) θ
    exact continuousAt_const.smul (ContinuousAt.comp (g := F) (f := fun z => z + a θ • u)
      (hF.continuousAt (hU.mem_nhds hmem)) (continuous_add_right _).continuousAt)
end ReciprocityTheory.ChartRestriction.DS.S7
