-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.UnitA.pr_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:34:44.547277+00:00
-- url     : https://prove2.me/submissions/7238231a-e4fc-4c08-8e85-48555d3b62ac

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
namespace ReciprocityTheory.ChartRestriction.DS.UnitA
theorem _root_.solution {a b : G → ℂ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    Integrable (fun x => star (a x) * b x) μ := by
  have h := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (ha.toLp a) (hb.toLp b)
  refine h.congr ?_
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hx1 hx2
  rw [hx1, hx2, RCLike.inner_apply, starRingEnd_apply, mul_comm]
end ReciprocityTheory.ChartRestriction.DS.UnitA
