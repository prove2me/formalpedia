-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.UnitA.pr_rt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:52:56.210525+00:00
-- url     : https://prove2.me/submissions/ca3384b4-39ed-4160-ae00-727e5f12ada7

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
theorem _root_.solution (a b : G → ℂ) (g : G) :
    pr μ (fun x => a (x * g)) (fun x => b (x * g)) = pr μ a b := by
  unfold pr
  exact integral_mul_right_eq_self (fun x => star (a x) * b x) g
end ReciprocityTheory.ChartRestriction.DS.UnitA
