-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.cca_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:15.065147+00:00
-- url     : https://prove2.me/submissions/2c69db97-68d7-401a-90ba-a79a6c62ca39

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
theorem _root_.solution {U : Set X} (hU : IsOpen U) {z₀ : X} (hz₀ : z₀ ∈ U) (u : X) :
    ∃ δ > 0, ∃ ρ > 0, ∀ z ∈ closedBall z₀ δ, ∀ t ∈ closedBall (0 : ℂ) ρ, z + t • u ∈ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  refine ⟨ε / 2, by positivity, ε / (2 * (‖u‖ + 1)), by positivity, fun z hz t ht => hball ?_⟩
  rw [Metric.mem_ball, dist_eq_norm]
  rw [Metric.mem_closedBall, dist_eq_norm] at hz ht
  rw [sub_zero] at ht
  have h1 : ‖t • u‖ ≤ ε / (2 * (‖u‖ + 1)) * ‖u‖ := by
    rw [norm_smul]; exact mul_le_mul_of_nonneg_right ht (norm_nonneg _)
  have h2 : ε / (2 * (‖u‖ + 1)) * ‖u‖ < ε / 2 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg u]
  calc ‖z + t • u - z₀‖ = ‖(z - z₀) + t • u‖ := by congr 1; abel
    _ ≤ ‖z - z₀‖ + ‖t • u‖ := norm_add_le _ _
    _ < ε := by linarith
end ReciprocityTheory.ChartRestriction.DS.S7
