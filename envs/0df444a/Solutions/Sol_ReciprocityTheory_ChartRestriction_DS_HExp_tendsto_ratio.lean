-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HExp.tendsto_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:10:00.33836+00:00
-- url     : https://prove2.me/submissions/6e5a3e08-6367-48ab-b80f-61a9881299b5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HExp
open MeasureTheory Metric Filter Topology Module
open scoped ENNReal NNReal
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable (lam nu : Measure V) [lam.IsAddHaarMeasure] [IsFiniteMeasure nu]
namespace ReciprocityTheory.ChartRestriction.DS.HExp
theorem _root_.solution {c : ℝ≥0∞}
    (hup : ∀ C : ℝ≥0, c < C → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, nu s ≤ C * lam s)
    (hdown : ∀ C : ℝ≥0, (C : ℝ≥0∞) < c → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, C * lam s ≤ nu s)
    (S : ℝ → Set V) (hS : ∀ δ > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ), S r ⊆ ball 0 δ)
    (hS0 : ∀ᶠ r in 𝓝[>] (0 : ℝ), lam (S r) ≠ 0 ∧ lam (S r) ≠ ⊤) :
    Tendsto (fun r => nu (S r) / lam (S r)) (𝓝[>] 0) (𝓝 c) := by
  rw [tendsto_order]
  constructor
  · intro C hC
    obtain ⟨C', hC'1, hC'2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hC
    obtain ⟨δ, hδ, h⟩ := hdown C' hC'2
    filter_upwards [hS δ hδ, hS0] with r hr hr0
    exact lt_of_lt_of_le hC'1 ((ENNReal.le_div_iff_mul_le (Or.inl hr0.1) (Or.inl hr0.2)).mpr (h _ hr))
  · intro C hC
    obtain ⟨C', hC'1, hC'2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hC
    obtain ⟨δ, hδ, h⟩ := hup C' hC'1
    filter_upwards [hS δ hδ, hS0] with r hr hr0
    exact lt_of_le_of_lt ((ENNReal.div_le_iff hr0.1 hr0.2).mpr (h _ hr)) hC'2
end ReciprocityTheory.ChartRestriction.DS.HExp
