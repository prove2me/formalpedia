-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HExp.Chart.img_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:55.19778+00:00
-- url     : https://prove2.me/submissions/89a37a53-c929-4704-b774-d0e6c896f25f

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
namespace ReciprocityTheory.ChartRestriction.DS.HExp.Chart
theorem _root_.solution (s : Set V) : C.img s = C.expG '' s := by
  ext g
  constructor
  · rintro ⟨X, hX, h⟩
    exact ⟨X, hX, C.emb.injective (by rw [mat_expG, h])⟩
  · rintro ⟨X, hX, rfl⟩
    exact ⟨X, hX, C.mat_expG X⟩
end ReciprocityTheory.ChartRestriction.DS.HExp.Chart
