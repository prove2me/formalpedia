-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.UnitA.pr_sub_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:15:38.952521+00:00
-- url     : https://prove2.me/submissions/b88692a2-e616-44dd-9095-108fdef1483e

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
theorem _root_.solution {a a₁ b : G → ℂ} (ha : MemLp a 2 μ) (ha₁ : MemLp a₁ 2 μ) (hb : MemLp b 2 μ) :
    pr μ (fun x => a x - a₁ x) b = pr μ a b - pr μ a₁ b := by
  unfold pr
  rw [← integral_sub (pr_int ha hb) (pr_int ha₁ hb)]
  congr 1
  funext x
  rw [star_sub, sub_mul]
end ReciprocityTheory.ChartRestriction.DS.UnitA
