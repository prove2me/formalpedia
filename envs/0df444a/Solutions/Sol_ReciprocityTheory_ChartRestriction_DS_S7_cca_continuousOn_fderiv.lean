-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.cca_continuousOn_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:28:45.59778+00:00
-- url     : https://prove2.me/submissions/fa022279-0efb-48e0-accb-79663914e79e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_cca_contAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_cca_kappa_cont
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_cca_local_formula

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
theorem _root_.solution [FiniteDimensional ℂ X] [CompleteSpace E] {F : X → E} {U : Set X}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) : ContinuousOn (fderiv ℂ F) U := by
  rw [continuousOn_clm_apply]
  intro u z₀ hz₀
  obtain ⟨δ, hδ, ρ, hρ, hsub, heq⟩ := cca_local_formula hU hF hz₀ u
  have hc := cca_contAt hU hF.continuousOn (cca_kappa_cont hρ) (continuous_circleMap 0 ρ) hδ hsub
  have hev : (fun z => fderiv ℂ F z u) =ᶠ[𝓝 z₀] fun z => (2 * π * I)⁻¹ •
      ∫ θ in (0 : ℝ)..2 * π, ccaKappa ρ θ • F (z + circleMap 0 ρ θ • u) := by
    filter_upwards [closedBall_mem_nhds z₀ hδ] with z hz using heq z hz
  exact ((hc.const_smul ((2 * π * I)⁻¹)).congr hev.symm).continuousWithinAt
end ReciprocityTheory.ChartRestriction.DS.S7
