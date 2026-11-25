-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.TopClm.opNorm_le_one_of_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:12:48.545558+00:00
-- url     : https://prove2.me/submissions/65590741-6949-4e96-9dc3-e250525b6a9c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_BesselVectors_ClmInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.TopClm
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
namespace ReciprocityTheory.ChartRestriction.DS.Lap.TopClm
theorem _root_.solution (A : V →L[ℂ] V) (hA : ∀ v, ‖A v‖ = ‖v‖) : ‖A‖ ≤ 1 := A.opNorm_le_bound zero_le_one fun v => by rw [hA, one_mul]
end ReciprocityTheory.ChartRestriction.DS.Lap.TopClm
