-- Prove2me | solution 1 for XuMannorRobust.WeakRobust.theorem8_sufficiency_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:12:51.94029+00:00
-- url     : https://prove2.me/submissions/84138bfa-6f5a-462e-9716-2eba6d527113

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

private theorem avg_mean {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z)
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

private theorem avg_bounds {Z H : Type*} (l : H → Z → ℝ) (M : ℝ)
    (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M)
    {n : ℕ} (hn : 0 < n) (h : H) (t : Fin n → Z) :
    0 ≤ avgLoss l h t ∧ avgLoss l h t ≤ M := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  unfold avgLoss
  constructor
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => (hl_bound h (t i)).1)
  · have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hl_bound h (t i)).2)
    have hh' : ∑ i, l h (t i) ≤ (n : ℝ) * M := by simpa using hh
    rw [one_div, ← div_eq_inv_mul, div_le_iff₀ hn']
    simpa only [mul_comm] using hh'

private theorem avg_measurable {Z H : Type*} [MeasurableSpace Z] (l : H → Z → ℝ)
    (hl_meas : ∀ h, Measurable (l h)) {n : ℕ} (h : H) :
    Measurable (avgLoss (n := n) l h) := by
  unfold avgLoss
  fun_prop

theorem _root_.solution {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (l : H → Z → ℝ) (M : ℝ)
    (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M) (hl_meas : ∀ h, Measurable (l h))
    {n : ℕ} (hn : 0 < n) (h : H) (s : Fin n → Z) (D : Set (Fin n → Z))
    (δ ε : ℝ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hD : Measure.pi (fun _ : Fin n => μ) Dᶜ ≤ ENNReal.ofReal δ)
    (hDε : ∀ t ∈ D, |avgLoss l h t - avgLoss l h s| ≤ ε) :
    |expectedLoss μ l h - avgLoss l h s| ≤ δ * M + ε := by
  classical
  let P := Measure.pi (fun _ : Fin n => μ)
  let a := avgLoss (n := n) l h
  let B := {t | ε < |a t - a s|}
  have hM : 0 ≤ M := (hl_bound h (s ⟨0, hn⟩)).1.trans (hl_bound h (s ⟨0, hn⟩)).2
  have ham : Measurable a := avg_measurable l hl_meas h
  have hBm : MeasurableSet B := measurableSet_lt measurable_const (by fun_prop : Measurable (fun t => |a t - a s|))
  have hBP : P B ≤ ENNReal.ofReal δ := by
    apply le_trans (measure_mono ?_) hD
    intro t ht
    exact fun htD => (not_lt_of_ge (hDε t htD)) ht
  have hBR : P.real B ≤ δ := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hBP).trans_eq (ENNReal.toReal_ofReal hδ)
  have hai : Integrable a P := avg_integrable μ l M hl_bound hl_meas h
  have hfi : Integrable (fun t => a t - a s) P := hai.sub (integrable_const _)
  have hBi : Integrable (B.indicator fun _ => M) P := (integrable_const M).indicator hBm
  have hpoint (t : Fin n → Z) : |a t - a s| ≤ ε + B.indicator (fun _ => M) t := by
    have ht := avg_bounds l M hl_bound hn h t
    have hs := avg_bounds l M hl_bound hn h s
    by_cases hb : t ∈ B
    · rw [Set.indicator_of_mem hb]
      have hab : |a t - a s| ≤ M := abs_le.mpr ⟨by dsimp [a]; linarith, by dsimp [a]; linarith⟩
      linarith
    · rw [Set.indicator_of_notMem hb]
      exact (le_of_not_gt hb).trans_eq (add_zero ε).symm
  calc
    |expectedLoss μ l h - a s| = |∫ t, a t - a s ∂P| := by
      rw [integral_sub hai (integrable_const _), integral_const]
      simp only [MeasureTheory.probReal_univ, one_smul]
      rw [avg_mean μ l M hl_bound hl_meas hn h]
    _ ≤ ∫ t, |a t - a s| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ t, ε + B.indicator (fun _ => M) t ∂P :=
      integral_mono hfi.abs ((integrable_const ε).add hBi) hpoint
    _ = ε + P.real B * M := by
      rw [integral_add (integrable_const ε) hBi, integral_const, integral_indicator_const M hBm]
      simp
    _ ≤ δ * M + ε := by nlinarith [mul_le_mul_of_nonneg_right hBR hM]
