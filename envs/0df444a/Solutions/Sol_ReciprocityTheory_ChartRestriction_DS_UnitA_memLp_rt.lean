-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.UnitA.memLp_rt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:07:33.020103+00:00
-- url     : https://prove2.me/submissions/29e171fc-d266-4e6b-8848-74072ac3adf8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_UnitarizeA

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
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.UnitA
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] (μ : Measure G)
variable {μ}
variable [μ.IsMulRightInvariant]
namespace ReciprocityTheory.ChartRestriction.DS.UnitA
theorem _root_.solution {a : G → ℂ} (ha : MemLp a 2 μ) (g : G) : MemLp (fun x => a (x * g)) 2 μ := by
  exact ha.comp_measurePreserving (measurePreserving_mul_right μ g)
end ReciprocityTheory.ChartRestriction.DS.UnitA
