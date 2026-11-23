-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.UnitA.pr_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:52:56.288337+00:00
-- url     : https://prove2.me/submissions/328c60d9-cbbc-460b-93cc-ea8868ec66d8

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
theorem _root_.solution (a b : G → ℂ) : star (pr μ a b) = pr μ b a := by
  unfold pr
  have h : ∫ x, (starRingEnd ℂ) (star (a x) * b x) ∂μ =
      (starRingEnd ℂ) (∫ x, star (a x) * b x ∂μ) := integral_conj
  simp only [starRingEnd_apply] at h
  rw [← h]
  congr 1
  funext x
  rw [star_mul, star_star]
end ReciprocityTheory.ChartRestriction.DS.UnitA
