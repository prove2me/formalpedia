-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.UnitA.pr_eq_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:15:24.160633+00:00
-- url     : https://prove2.me/submissions/7d05c8b7-cc08-4f2a-a801-290b352ece75

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
    pr μ a b = inner ℂ (ha.toLp a) (hb.toLp b) := by
  rw [MeasureTheory.L2.inner_def]
  unfold pr
  apply integral_congr_ae
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hx1 hx2
  rw [hx1, hx2, RCLike.inner_apply, starRingEnd_apply, mul_comm]
end ReciprocityTheory.ChartRestriction.DS.UnitA
