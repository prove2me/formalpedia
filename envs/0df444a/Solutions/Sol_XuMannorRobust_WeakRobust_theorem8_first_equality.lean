-- Prove2me | solution 1 for XuMannorRobust.WeakRobust.theorem8_first_equality
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:11:24.74668+00:00
-- url     : https://prove2.me/submissions/c95f2214-0906-49f4-bce1-28d010d23b07

import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic
import Definitions.Def_XuMannorRobust_WeakRobust_Setup
open MeasureTheory Filter Topology XuMannorRobust.WeakRobust
open scoped BigOperators
noncomputable section

private theorem loss_integrable {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (l : H → Z → ℝ) (M : ℝ)
    (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M) (hl_meas : ∀ h, Measurable (l h))
    (h : H) : Integrable (l h) μ := by
  apply (integrable_const M).mono' (hl_meas h).aestronglyMeasurable
  exact Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hl_bound h z).1] using (hl_bound h z).2

private theorem avg_integrable {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (l : H → Z → ℝ) (M : ℝ)
    (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M) (hl_meas : ∀ h, Measurable (l h))
    {n : ℕ} (h : H) : Integrable (avgLoss (n := n) l h) (Measure.pi fun _ : Fin n => μ) := by
  unfold avgLoss
  apply Integrable.const_mul
  apply integrable_finset_sum
  intro i _
  exact integrable_comp_eval (loss_integrable μ l M hl_bound hl_meas h)

theorem _root_.solution {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (l : H → Z → ℝ) (M : ℝ)
    (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M) (hl_meas : ∀ h, Measurable (l h))
    {n : ℕ} (hn : 0 < n) (h : H) :
    ∫ t, avgLoss l h t ∂(Measure.pi fun _ : Fin n => μ) = expectedLoss μ l h := by
  unfold avgLoss expectedLoss
  rw [integral_const_mul, integral_finset_sum]
  · simp_rw [integral_comp_eval (μ := fun _ : Fin n => μ) (hl_meas h).aestronglyMeasurable]
    simp [ne_of_gt hn]
  · intro i _
    exact integrable_comp_eval (loss_integrable μ l M hl_bound hl_meas h)
