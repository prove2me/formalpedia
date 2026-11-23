-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HExp.Chart.expG_cont
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:04:47.10029+00:00
-- url     : https://prove2.me/submissions/d48260be-5141-4c5f-9d24-d6a780b7490e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_exp_cont
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
namespace ReciprocityTheory.ChartRestriction.DS.HExp.Chart
theorem _root_.solution : Continuous C.expG := by
  rw [C.emb.isInducing.continuous_iff]
  have : C.mat ∘ C.expG = fun X : V => exp (X : 𝔸) := funext C.mat_expG
  rw [this]
  exact exp_cont.comp continuous_subtype_val
end ReciprocityTheory.ChartRestriction.DS.HExp.Chart
