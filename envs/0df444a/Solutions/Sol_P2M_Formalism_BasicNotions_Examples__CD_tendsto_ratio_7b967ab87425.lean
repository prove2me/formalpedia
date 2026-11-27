-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_tendsto_ratio_7b967ab87425
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:50:36.123972+00:00
-- url     : https://prove2.me/submissions/ec70cf8a-82db-4e21-8de3-99318b6927d4

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LeOfEventuallyDown

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Metric Filter Topology Module
open scoped ENNReal NNReal
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable (lam nu : Measure V) [lam.IsAddHaarMeasure] [IsFiniteMeasure nu]
namespace Formalism.BasicNotions.Examples₂.CD
theorem _root_.solution {c : ℝ≥0∞}
    (hup : ∀ C : ℝ≥0, c < C → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, nu s ≤ C * lam s)
    (hdown : ∀ C : ℝ≥0, (C : ℝ≥0∞) < c → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, C * lam s ≤ nu s)
    (S : ℝ → Set V) (hS : ∀ δ > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ), S r ⊆ ball 0 δ)
    (hS0 : ∀ᶠ r in 𝓝[>] (0 : ℝ), lam (S r) ≠ 0 ∧ lam (S r) ≠ ⊤) :
    Tendsto (fun r => nu (S r) / lam (S r)) (𝓝[>] 0) (𝓝 c) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨C, haC, hCc⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp ha
    obtain ⟨δ, hδ, hd⟩ := hdown C hCc
    filter_upwards [hS δ hδ, hS0] with r hr h0
    refine lt_of_lt_of_le haC ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inl h0.1) (Or.inl h0.2)]
    exact hd (S r) hr
  · obtain ⟨C, hcC, hCb⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hb
    obtain ⟨δ, hδ, hu⟩ := hup C hcC
    filter_upwards [hS δ hδ] with r hr
    exact lt_of_le_of_lt (ENNReal.div_le_of_le_mul (hu (S r) hr)) hCb
end Formalism.BasicNotions.Examples₂.CD
