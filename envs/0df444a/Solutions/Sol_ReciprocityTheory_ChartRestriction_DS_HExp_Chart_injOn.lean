-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HExp.Chart.injOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:55.198419+00:00
-- url     : https://prove2.me/submissions/c006f806-5c26-43c8-b207-a5de030fedd0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_mat_expG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HExp
open MeasureTheory Filter Topology Metric NormedSpace Set
open scoped ENNReal NNReal
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
open ReciprocityTheory.ChartRestriction.DS.HExp.Chart
variable {V : Submodule ℝ 𝔸} {G : Type*} [Group G] [TopologicalSpace G] (C : Chart V G)
variable {ρ : ℝ} (hR : ∀ Z : 𝔸, ‖Z‖ < ρ → logA 𝔸 (exp Z) = Z ∧ ((∃ g, C.mat g = exp Z) → Z ∈ V))
include hR
namespace ReciprocityTheory.ChartRestriction.DS.HExp.Chart
theorem _root_.solution : InjOn C.expG (ball (0 : V) ρ) := by
  intro X hX Y hY h
  have hX' : ‖(X : 𝔸)‖ < ρ := by simpa using hX
  have hY' : ‖(Y : 𝔸)‖ < ρ := by simpa using hY
  have e : exp (X : 𝔸) = exp (Y : 𝔸) := by rw [← C.mat_expG, ← C.mat_expG, h]
  exact Subtype.ext (by rw [← (hR _ hX').1, e, (hR _ hY').1])
end ReciprocityTheory.ChartRestriction.DS.HExp.Chart
