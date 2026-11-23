-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.cca_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:58.920965+00:00
-- url     : https://prove2.me/submissions/d1e15a92-4da2-48f0-80f1-4ffb15628a56

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA

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
theorem _root_.solution {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ X]
    {F : X → G} {U : Set X} (hF : ContinuousOn F U) {κ a : ℝ → ℂ} (hκ : Continuous κ)
    (ha : Continuous a) {z₀ u : X} {δ : ℝ} (hsub : ∀ z ∈ closedBall z₀ δ, ∀ θ, z + a θ • u ∈ U) :
    ∃ B : ℝ, ∀ z ∈ closedBall z₀ δ, ∀ θ ∈ Set.uIoc (0 : ℝ) (2 * π), ‖κ θ • F (z + a θ • u)‖ ≤ B := by
  have hK : IsCompact (closedBall z₀ δ ×ˢ Set.uIcc (0 : ℝ) (2 * π)) :=
    (isCompact_closedBall z₀ δ).prod isCompact_uIcc
  have hc : ContinuousOn (fun p : X × ℝ => κ p.2 • F (p.1 + a p.2 • u))
      (closedBall z₀ δ ×ˢ Set.uIcc (0 : ℝ) (2 * π)) := by
    refine (hκ.comp continuous_snd).continuousOn.smul ?_
    refine hF.comp (f := fun p : X × ℝ => p.1 + a p.2 • u)
      (continuous_fst.add ((ha.comp continuous_snd).smul continuous_const)).continuousOn ?_
    intro p hp
    exact hsub p.1 hp.1 p.2
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc
  exact ⟨B, fun z hz θ hθ => hB (z, θ) ⟨hz, Set.uIoc_subset_uIcc hθ⟩⟩
end ReciprocityTheory.ChartRestriction.DS.S7
