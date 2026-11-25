-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HExp.Chart.meas_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:13:06.029768+00:00
-- url     : https://prove2.me/submissions/4d238561-bef7-407a-9a39-f361fdafeb87

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_expG_cont
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_injOn

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
variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace G] [BorelSpace G]
include hR
namespace ReciprocityTheory.ChartRestriction.DS.HExp.Chart
theorem _root_.solution {s : Set V} (hs : MeasurableSet s) (hsub : s ⊆ ball 0 ρ) :
    MeasurableSet (C.expG '' s) := by
  have : T2Space G := C.emb.t2Space
  exact hs.image_of_continuousOn_injOn C.expG_cont.continuousOn ((C.injOn hR).mono hsub)
end ReciprocityTheory.ChartRestriction.DS.HExp.Chart
