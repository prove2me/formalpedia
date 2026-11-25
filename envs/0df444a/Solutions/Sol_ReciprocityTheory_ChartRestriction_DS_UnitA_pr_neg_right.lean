-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.UnitA.pr_neg_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:15:31.055177+00:00
-- url     : https://prove2.me/submissions/4cf808c2-8e79-408e-9c9e-c8ed1913fc66

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
theorem _root_.solution (a b : G → ℂ) : pr μ a (fun x => -b x) = -pr μ a b := by
  unfold pr
  rw [← integral_neg]
  congr 1
  funext x
  rw [mul_neg]
end ReciprocityTheory.ChartRestriction.DS.UnitA
