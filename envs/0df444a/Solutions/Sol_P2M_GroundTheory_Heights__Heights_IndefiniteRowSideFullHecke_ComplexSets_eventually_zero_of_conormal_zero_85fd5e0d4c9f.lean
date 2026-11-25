-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eventually_zero_of_conormal_zero_85fd5e0d4c9f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:06:40.290424+00:00
-- url     : https://prove2.me/submissions/d9ef1b36-9a5d-49f0-940d-3d8741cf54e3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularLocusDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticImplicitChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegularLocusDense
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eventually_zero_of_iteratedFDeriv_diag_0fad6a438363
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_iteratedFDeriv_succ_diag_eq_14b5d008132d

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
open Topology Filter Module
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {C : Set E} {y₀ : E} (hy₀ : y₀ ∈ C) {U : Set E} (hU : U ∈ 𝓝 y₀)
    (hC : ∀ c ∈ C ∩ U, ∀ ψ : E → ℂ, AnalyticAt ℂ ψ c → (∀ᶠ u in 𝓝 c, u ∈ C → ψ u = 0) →
      fderiv ℂ ψ c = 0)
    {ψ : E → ℂ} (hψ : AnalyticAt ℂ ψ y₀) (hψC : ∀ᶠ u in 𝓝 y₀, u ∈ C → ψ u = 0) :
    ∀ᶠ u in 𝓝 y₀, ψ u = 0 := by
  have step : ∀ φ : E → ℂ, AnalyticAt ℂ φ y₀ → (∀ᶠ u in 𝓝 y₀, u ∈ C → φ u = 0) → ∀ v : E,
      AnalyticAt ℂ (fun y => fderiv ℂ φ y v) y₀ ∧ ∀ᶠ u in 𝓝 y₀, u ∈ C → fderiv ℂ φ u v = 0 := by
    intro φ hφ hφC v
    refine ⟨((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp hφ.fderiv, ?_⟩
    filter_upwards [hφ.eventually_analyticAt, hφC.eventually_nhds, hU] with c hca hcC hcU hc
    rw [hC c ⟨hc, hcU⟩ φ hca hcC]
    rfl
  have key : ∀ n : ℕ, ∀ φ : E → ℂ, AnalyticAt ℂ φ y₀ → (∀ᶠ u in 𝓝 y₀, u ∈ C → φ u = 0) →
      ∀ v : E, iteratedFDeriv ℂ n φ y₀ (fun _ => v) = 0 := by
    intro n
    induction n with
    | zero => intro φ _ hφC v; simpa using hφC.self_of_nhds hy₀
    | succ n ih =>
      intro φ hφ hφC v
      rw [iteratedFDeriv_succ_diag_eq hφ]
      obtain ⟨h1, h2⟩ := step φ hφ hφC v
      exact ih _ h1 h2 v
  exact eventually_zero_of_iteratedFDeriv_diag hψ fun n v => key n ψ hψ hψC v
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
