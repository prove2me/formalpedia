-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.UnitA.pr_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:15:35.623896+00:00
-- url     : https://prove2.me/submissions/38e331e6-4422-43ce-b3e1-ea3dcb15bc32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_UnitarizeA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitA_pr_rt

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
    pr μ (fun x => a (x * g)) b = pr μ a (fun x => b (x * g⁻¹)) := by
  rw [← pr_rt (fun x => a (x * g)) b g⁻¹]
  simp only [inv_mul_cancel_right, mul_inv_cancel_right]
end ReciprocityTheory.ChartRestriction.DS.UnitA
