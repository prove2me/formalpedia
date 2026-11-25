-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:38:34.297298+00:00
-- url     : https://prove2.me/submissions/f918d89d-db82-4b9a-987e-c58a42b376e3

import Mathlib
import Definitions.Def_Lemmata_FirstBlockLemmaJ_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EqZeroOfMulEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_eq_zero_of_eventually

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
theorem _root_.solution {U : Set V} (hU : IsOpen U) (hc : IsPreconnected U) {f g : V → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) (hfg : ∀ y ∈ U, f y * g y = 0)
    {x0 : V} (hx0 : x0 ∈ U) (h0 : f x0 ≠ 0) : ∀ y ∈ U, g y = 0 := by
  refine eq_zero_of_eventually hU hc hg hx0 ?_
  have h1 : ∀ᶠ y in 𝓝 x0, f y ≠ 0 := (hf.continuousOn.continuousAt (hU.mem_nhds hx0)).eventually_ne h0
  filter_upwards [h1, hU.mem_nhds hx0] with y hy hyU
  exact (mul_eq_zero.mp (hfg y hyU)).resolve_left hy
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
