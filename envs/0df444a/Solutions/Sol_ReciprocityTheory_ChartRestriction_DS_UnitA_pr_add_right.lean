-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.UnitA.pr_add_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:07:15.690427+00:00
-- url     : https://prove2.me/submissions/a37b8156-1447-4495-861f-81a99483a780

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_UnitarizeA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitA_pr_int

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
theorem _root_.solution {a b b₁ : G → ℂ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) (hb₁ : MemLp b₁ 2 μ) :
    pr μ a (b + b₁) = pr μ a b + pr μ a b₁ := by
  unfold pr
  rw [← integral_add (pr_int ha hb) (pr_int ha hb₁)]
  congr 1
  funext x
  simp only [Pi.add_apply, mul_add]
end ReciprocityTheory.ChartRestriction.DS.UnitA
