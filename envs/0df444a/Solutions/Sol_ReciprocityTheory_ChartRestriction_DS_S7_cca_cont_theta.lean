-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.cca_cont_theta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:58.49417+00:00
-- url     : https://prove2.me/submissions/16dbe75f-f356-4780-b8d2-ed7db7a8f8e5

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
theorem _root_.solution {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] {F : X → G} {U : Set X}
    (hF : ContinuousOn F U) {κ a : ℝ → ℂ} (hκ : Continuous κ) (ha : Continuous a) {z u : X}
    (hz : ∀ θ, z + a θ • u ∈ U) : Continuous (fun θ => κ θ • F (z + a θ • u)) := hκ.smul (hF.comp_continuous (continuous_const.add (ha.smul continuous_const)) hz)
end ReciprocityTheory.ChartRestriction.DS.S7
