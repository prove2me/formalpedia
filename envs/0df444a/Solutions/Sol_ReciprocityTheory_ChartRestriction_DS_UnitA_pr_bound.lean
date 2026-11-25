-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.UnitA.pr_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:22:09.025802+00:00
-- url     : https://prove2.me/submissions/ebda10da-0983-46d0-9629-298ef23be6f5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_UnitarizeA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitA_pr_eq_inner

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
    ‖pr μ a b‖ ≤ nrm μ a * nrm μ b := by
  rw [pr_eq_inner ha hb]
  have h := norm_inner_le_norm (𝕜 := ℂ) (ha.toLp a) (hb.toLp b)
  simpa only [nrm, Lp.norm_toLp] using h
end ReciprocityTheory.ChartRestriction.DS.UnitA
