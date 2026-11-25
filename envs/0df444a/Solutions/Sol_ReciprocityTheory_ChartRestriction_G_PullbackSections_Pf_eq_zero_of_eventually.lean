-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_eventually
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:32:20.39786+00:00
-- url     : https://prove2.me/submissions/327e508c-faaa-41b7-95cc-05ea507ed6ac

import Mathlib
import Definitions.Def_Lemmata_FirstBlockLemmaJ_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EqZeroOfMulEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_eq_zero_on_ball

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
open Metric Set Filter Topology
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
theorem _root_.solution {U : Set V} (hU : IsOpen U) (hc : IsPreconnected U) {g : V → ℂ}
    (hg : DifferentiableOn ℂ g U) {x0 : V} (hx0 : x0 ∈ U) (h0 : g =ᶠ[𝓝 x0] 0) : ∀ y ∈ U, g y = 0 := by
  have hZo : IsOpen {x : V | g =ᶠ[𝓝 x] 0} := isOpen_setOfPred_eventually_nhds
  have hsub : U ⊆ {x : V | g =ᶠ[𝓝 x] 0} := by
    refine hc.subset_of_closure_inter_subset hZo ⟨x0, hx0, h0⟩ ?_
    rintro x ⟨hxc, hxU⟩
    obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp hU x hxU
    obtain ⟨z, hzZ, hzd⟩ := Metric.mem_closure_iff.mp hxc ε hε
    have hzb : z ∈ ball x ε := by rw [mem_ball, dist_comm]; exact hzd
    have hall := eq_zero_on_ball (hg.mono hb) hzb hzZ
    exact Filter.eventually_of_mem (ball_mem_nhds x hε) hall
  intro y hy
  exact (hsub hy).self_of_nhds
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
