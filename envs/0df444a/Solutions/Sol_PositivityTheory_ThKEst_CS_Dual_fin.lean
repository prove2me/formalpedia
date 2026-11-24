-- Prove2me | solution 1 for PositivityTheory.ThKEst.CS.Dual.fin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:48.867029+00:00
-- url     : https://prove2.me/submissions/6951474e-22df-4741-8de9-be9e673fa29d

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_CoefSumA
import Theorems.Thm_PositivityTheory_ThKEst_CS_Dual_lint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology Filter
open scoped ENNReal ComplexConjugate Pointwise
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.CS
variable {G Γ : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [AddCommGroup Γ]
variable {r : Γ →+ G} {e : Γ → G → ℂ}
variable [MeasurableSpace G] [BorelSpace G] [Countable Γ] {μ : Measure G} [μ.IsAddHaarMeasure] {D : Set G}
namespace PositivityTheory.ThKEst.CS
namespace Dual
theorem _root_.solution (h : Dual r e) (hD : IsAddFundamentalDomain r.range D μ) : μ D ≠ ∞ := by
  obtain ⟨K, hK, hKc⟩ := h.cpt
  have hK' := hK.closure
  have hm : MeasurableSet (closure K) := isClosed_closure.measurableSet
  have h1 := h.lint hD ((closure K).indicator 1)
  have hmeas : ∀ ξ, AEMeasurable (fun u => (closure K).indicator (1 : G → ℝ≥0∞) (r ξ + u)) (μ.restrict D) := fun ξ =>
    ((measurable_one.indicator hm).comp (measurable_const_add _)).aemeasurable
  rw [lintegral_indicator_one hm, ← lintegral_tsum hmeas] at h1
  refine ne_top_of_le_ne_top (hK'.measure_lt_top (μ := μ)).ne ?_
  rw [h1, ← setLIntegral_one]
  refine lintegral_mono fun u => ?_
  obtain ⟨ξ, hξ⟩ := hKc u
  refine le_trans ?_ (ENNReal.le_tsum (-ξ))
  have : r (-ξ) + u ∈ closure K := subset_closure (by rwa [map_neg, neg_add_eq_sub])
  simp [Set.indicator_of_mem this, ← map_neg, -map_neg]
end Dual
end PositivityTheory.ThKEst.CS
