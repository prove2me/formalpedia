-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.cca_local_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:20:54.791153+00:00
-- url     : https://prove2.me/submissions/1d0d5665-6545-4ad4-9e31-3ca0059b4706

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_cca_loc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_cca_mem_disc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_cca_fderiv_eq

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
theorem _root_.solution [CompleteSpace E] {F : X → E} {U : Set X} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {z₀ : X} (hz₀ : z₀ ∈ U) (u : X) :
    ∃ δ > 0, ∃ ρ > 0, (∀ z ∈ closedBall z₀ δ, ∀ θ, z + circleMap 0 ρ θ • u ∈ U) ∧
      ∀ z ∈ closedBall z₀ δ, fderiv ℂ F z u = (2 * π * I)⁻¹ •
        ∫ θ in (0 : ℝ)..2 * π, ccaKappa ρ θ • F (z + circleMap 0 ρ θ • u) := by
  obtain ⟨δ, hδ, ρ, hρ, h⟩ := cca_loc hU hz₀ u
  exact ⟨δ, hδ, ρ, hρ, fun z hz θ => h z hz _ (cca_mem_disc hρ θ),
    fun z hz => cca_fderiv_eq hU hF hρ (h z hz)⟩
end ReciprocityTheory.ChartRestriction.DS.S7
