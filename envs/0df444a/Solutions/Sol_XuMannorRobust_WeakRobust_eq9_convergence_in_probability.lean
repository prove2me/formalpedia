-- Prove2me | solution 1 for XuMannorRobust.WeakRobust.eq9_convergence_in_probability
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:18:51.238828+00:00
-- url     : https://prove2.me/submissions/d4aea199-32c2-4a2a-aa91-a349f9057cd4

import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecificLimits.Basic
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

open ProbabilityTheory
private theorem sample_tail {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (l : H → Z → ℝ) (M : ℝ)
    (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M) (hl_meas : ∀ h, Measurable (l h))
    {n : ℕ} (hn : 0 < n) (h : H) (ε : ℝ) (hε : 0 < ε) :
    (Measure.pi (fun _ : Fin n => μ))
      {t | ε ≤ |avgLoss l h t - expectedLoss μ l h|} ≤ ENNReal.ofReal ((M^2 / ε^2) / n) := by
  let P := Measure.pi (fun _ : Fin n => μ)
  have hlp : MemLp (l h) 2 μ :=
    memLp_of_bounded (Eventually.of_forall fun z => hl_bound h z) (hl_meas h).aestronglyMeasurable 2
  have hap : MemLp (avgLoss (n := n) l h) 2 P :=
    memLp_of_bounded (Eventually.of_forall fun t => avg_bounds l M hl_bound hn h t)
      (avg_measurable l hl_meas h).aestronglyMeasurable 2
  have hv : variance (l h) μ ≤ M^2 := by
    have hh := variance_le_sq_of_bounded (μ := μ) (Eventually.of_forall fun z => hl_bound h z) (hl_meas h).aemeasurable
    simp only [sub_zero] at hh
    nlinarith [sq_nonneg M]
  have hvar : variance (avgLoss (n := n) l h) P = (1 / (n : ℝ))^2 * ((n : ℝ) * variance (l h) μ) := by
    unfold avgLoss
    rw [variance_const_mul]
    have heq : (fun t : Fin n → Z => ∑ i, l h (t i)) = ∑ i : Fin n, (fun t : Fin n → Z => l h (t i)) := by
      ext t
      simp only [Finset.sum_apply]
    rw [heq, variance_sum_pi (fun _ => hlp)]
    simp
  have hh := meas_ge_le_variance_div_sq hap hε
  rw [avg_mean μ l M hl_bound hl_meas hn h] at hh
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  rw [hvar]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have he' : 0 < ε^2 := sq_pos_of_pos hε
  have hv' := mul_le_mul_of_nonneg_left hv (show 0 ≤ (1 / (n : ℝ))^2 * (n : ℝ) by positivity)
  apply (div_le_iff₀ he').2
  have heq : (M^2 / ε^2 / (n : ℝ)) * ε^2 = M^2 / n := by field_simp
  rw [heq]
  have heq' : (1 / (n : ℝ))^2 * ((n : ℝ) * variance (l h) μ) = variance (l h) μ / n := by field_simp
  rw [heq']
  exact div_le_div_of_nonneg_right hv hn'.le

theorem _root_.solution {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (l : H → Z → ℝ) (M : ℝ)
    (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M) (hl_meas : ∀ h, Measurable (l h))
    (A : (n : ℕ) → (Fin n → Z) → H) (sStar : ℕ → Z) :
    ∀ ε > 0, Tendsto
      (fun n => Measure.pi (fun _ : Fin n => μ)
        {t | ε ≤ |avgLoss l (A n (firstN sStar n)) t - expectedLoss μ l (A n (firstN sStar n))|})
      atTop (𝓝 0) := by
  intro ε hε
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal ((M^2 / ε^2) / n)) atTop (𝓝 0) := by
    have hh : Tendsto (fun n : ℕ => (M^2 / ε^2) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using ENNReal.tendsto_ofReal hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n => bot_le)
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact sample_tail μ l M hl_bound hl_meas (by omega) (A n (firstN sStar n)) ε hε
