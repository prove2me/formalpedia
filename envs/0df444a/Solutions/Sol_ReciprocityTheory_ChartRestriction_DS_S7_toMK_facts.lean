-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.toMK_facts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:05:41.53795+00:00
-- url     : https://prove2.me/submissions/ddf77d96-5050-407d-bf92-8e5be4498057

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {ε : Fin n → Bool}
open PolarDecomposition
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (k : KG ε) : (toMK k)ᴴ * toMK k = 1 ∧ toMK k * (toMK k)ᴴ = 1 ∧
    toMK k * Jm ε = Jm ε * toMK k := by
  have hk : toMK k ∈ Kset ε := k.2
  obtain ⟨hu, hc⟩ := hk
  refine ⟨?_, ?_, hc⟩
  · have h := Matrix.mem_unitaryGroup_iff'.1 hu
    rwa [Matrix.star_eq_conjTranspose] at h
  · have h := Matrix.mem_unitaryGroup_iff.1 hu
    rwa [Matrix.star_eq_conjTranspose] at h
end ReciprocityTheory.ChartRestriction.DS.S7
