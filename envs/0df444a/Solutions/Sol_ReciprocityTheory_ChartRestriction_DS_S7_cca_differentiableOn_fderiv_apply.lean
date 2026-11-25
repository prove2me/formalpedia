-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.cca_differentiableOn_fderiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:35:38.325397+00:00
-- url     : https://prove2.me/submissions/672f7d1a-aa80-4f4a-b46c-06cfafffbc95

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_cca_hasFDerivAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_cca_kappa_cont
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_cca_local_formula
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_cca_continuousOn_fderiv

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
theorem _root_.solution [FiniteDimensional ℂ X] [CompleteSpace E] {F : X → E}
    {U : Set X} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (u : X) :
    DifferentiableOn ℂ (fun z => fderiv ℂ F z u) U := by
  intro z₀ hz₀
  obtain ⟨δ, hδ, ρ, hρ, hsub, heq⟩ := cca_local_formula hU hF hz₀ u
  have hD := cca_continuousOn_fderiv hU hF
  have hfd := cca_hasFDerivAt hU hF hD (cca_kappa_cont hρ) (continuous_circleMap 0 ρ) hδ hsub
  have hev : (fun z => fderiv ℂ F z u) =ᶠ[𝓝 z₀] fun z => (2 * π * I)⁻¹ •
      ∫ θ in (0 : ℝ)..2 * π, ccaKappa ρ θ • F (z + circleMap 0 ρ θ • u) := by
    filter_upwards [closedBall_mem_nhds z₀ hδ] with z hz using heq z hz
  exact ((hfd.const_smul ((2 * π * I)⁻¹)).differentiableAt.congr_of_eventuallyEq hev).differentiableWithinAt
end ReciprocityTheory.ChartRestriction.DS.S7
