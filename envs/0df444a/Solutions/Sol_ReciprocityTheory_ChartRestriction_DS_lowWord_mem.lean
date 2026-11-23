-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.lowWord_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:36:05.098392+00:00
-- url     : https://prove2.me/submissions/8acf99f4-ae9e-4e13-a86e-67376248dea3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {y : M} {l : List (Fin n × Fin n)} (hl : ∀ p ∈ l, IsKLow ε p) :
    lowWord E y l ∈ kLowSpan ε E y := by
  unfold kLowSpan
  exact Submodule.subset_span ⟨l, hl, rfl⟩
end ReciprocityTheory.ChartRestriction.DS
