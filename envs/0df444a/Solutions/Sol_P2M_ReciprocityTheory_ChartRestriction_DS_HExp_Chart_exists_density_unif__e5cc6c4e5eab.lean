-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_exists_density_unif__e5cc6c4e5eab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:06:54.826854+00:00
-- url     : https://prove2.me/submissions/054b9500-fc21-496b-a5b1-ceb37ee03570

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_exists_density_unif

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
namespace ReciprocityTheory.ChartRestriction.DS.HExp
namespace Chart
theorem _root_.solution {V : Submodule ℝ 𝔸} {G : Type*} [Group G] [TopologicalSpace G]
    (C : Chart V G) (_hfd : FiniteDimensional ℝ V) (mV : MeasurableSpace V) (_hbV : BorelSpace V)
    (mG : MeasurableSpace G) (_hbG : BorelSpace G) (_hG : IsTopologicalGroup G)
    (μ : Measure G) (_hμ : μ.IsHaarMeasure) (lam : Measure V) (_hlam : lam.IsAddHaarMeasure) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      (∀ D : ℝ≥0, c < D → ∃ δ > 0, ∀ s : Set V, MeasurableSet s → s ⊆ ball (0 : V) δ →
        μ (C.img s) ≤ D * lam s) ∧
      (∀ D : ℝ≥0, (D : ℝ≥0∞) < c → ∃ δ > 0, ∀ s : Set V, MeasurableSet s → s ⊆ ball (0 : V) δ →
        D * lam s ≤ μ (C.img s)) :=
  C.exists_density_unif μ lam
end Chart
end ReciprocityTheory.ChartRestriction.DS.HExp
