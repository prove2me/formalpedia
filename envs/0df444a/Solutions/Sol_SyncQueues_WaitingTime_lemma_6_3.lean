-- Prove2me | solution 1 for SyncQueues.WaitingTime.lemma_6_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:37:27.480562+00:00
-- url     : https://prove2.me/submissions/f1d7dc57-460d-4108-901e-ecbb491f5e73

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₁ X₂ Y₁ Y₂ : Ω → ℝ)
    (hX₁ : AEStronglyMeasurable X₁ P) (hX₂ : AEStronglyMeasurable X₂ P)
    (hY₁ : AEStronglyMeasurable Y₁ P) (hY₂ : AEStronglyMeasurable Y₂ P)
    (hX₁0 : ∀ ω, 0 ≤ X₁ ω) (hX₂0 : ∀ ω, 0 ≤ X₂ ω) (hY₁0 : ∀ ω, 0 ≤ Y₁ ω) (hY₂0 : ∀ ω, 0 ≤ Y₂ ω)
    {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm (fun ω => max (X₁ ω) (X₂ ω) - max (Y₁ ω) (Y₂ ω)) (ENNReal.ofReal p) P ≤
      eLpNorm X₂ (ENNReal.ofReal p) P + eLpNorm Y₂ (ENNReal.ofReal p) P +
        eLpNorm (fun ω => X₁ ω - Y₁ ω) (ENNReal.ofReal p) P := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hpt : ∀ ω, ‖max (X₁ ω) (X₂ ω) - max (Y₁ ω) (Y₂ ω)‖
      ≤ X₂ ω + Y₂ ω + ‖X₁ ω - Y₁ ω‖ := by
    intro ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have a1 := hX₁0 ω; have a2 := hX₂0 ω; have a3 := hY₁0 ω; have a4 := hY₂0 ω
    have b1 := le_abs_self (X₁ ω - Y₁ ω); have b2 := neg_abs_le (X₁ ω - Y₁ ω)
    rw [abs_le]
    constructor
    · have := le_max_left (X₁ ω) (X₂ ω)
      have : max (Y₁ ω) (Y₂ ω) ≤ Y₁ ω + Y₂ ω := max_le (by linarith) (by linarith)
      linarith
    · have := le_max_left (Y₁ ω) (Y₂ ω)
      have : max (X₁ ω) (X₂ ω) ≤ X₁ ω + X₂ ω := max_le (by linarith) (by linarith)
      linarith
  have hD : AEStronglyMeasurable (fun ω => X₁ ω - Y₁ ω) P := hX₁.sub hY₁
  calc eLpNorm (fun ω => max (X₁ ω) (X₂ ω) - max (Y₁ ω) (Y₂ ω)) (ENNReal.ofReal p) P
      ≤ eLpNorm (fun ω => X₂ ω + Y₂ ω + ‖X₁ ω - Y₁ ω‖) (ENNReal.ofReal p) P :=
        eLpNorm_mono_real hpt
    _ ≤ eLpNorm (fun ω => X₂ ω + Y₂ ω) (ENNReal.ofReal p) P
          + eLpNorm (fun ω => ‖X₁ ω - Y₁ ω‖) (ENNReal.ofReal p) P :=
        eLpNorm_add_le (hX₂.add hY₂) hD.norm hp1
    _ ≤ eLpNorm X₂ (ENNReal.ofReal p) P + eLpNorm Y₂ (ENNReal.ofReal p) P
          + eLpNorm (fun ω => X₁ ω - Y₁ ω) (ENNReal.ofReal p) P := by
        rw [eLpNorm_norm (fun ω => X₁ ω - Y₁ ω)]
        gcongr
        exact eLpNorm_add_le hX₂ hY₂ hp1
