-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.layerWtVecs_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:22:10.482884+00:00
-- url     : https://prove2.me/submissions/62b6d224-d3d2-44db-b5dc-569aeed91e65

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_LayerSpan

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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {k l : ℕ} (h : k ≤ l) : layerWtVecs ε E V k ⊆ layerWtVecs ε E V l := by
  rintro w ⟨ν, ω, j, hj, hω, hv, hw⟩
  exact ⟨ν, ω, j, hj.trans h, hω, hv, hw⟩
end ReciprocityTheory.ChartRestriction.DS
