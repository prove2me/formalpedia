-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.exists_toMK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:17.198956+00:00
-- url     : https://prove2.me/submissions/8ae3ad47-d663-4db8-8c93-f65d2fe620f4

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
theorem _root_.solution {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : ∃ u : KG ε, toMK u = k := by
  obtain ⟨hu, hc⟩ := hk
  have h1 : k * kᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.1 hu
    rwa [Matrix.star_eq_conjTranspose] at h
  have h2 : kᴴ * k = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.1 hu
    rwa [Matrix.star_eq_conjTranspose] at h
  have hUJ : inUJ ε k := by
    unfold inUJ
    rw [mul_assoc, ← hc, ← mul_assoc, h2, one_mul]
  refine ⟨⟨⟨⟨k, kᴴ, h1, h2⟩, ?_⟩, ?_⟩, rfl⟩
  · exact hUJ
  · exact (⟨hu, hc⟩ : k ∈ Kset ε)
end ReciprocityTheory.ChartRestriction.DS.S7
