-- Prove2me | solution 1 for avram_chat24_uniform_step_DCT_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:12:59.685701+00:00
-- url     : https://prove2.me/submissions/ec9797fd-ce03-4e4f-8684-358d058e405b

import Mathlib
import Theorems.Thm_avram_chat24_uniform_step_pointwise_core
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    (μ : Measure ℝ≥0) [IsFiniteMeasure μ] (hzero : μ {0} = 0)
    (F Y : ℝ≥0 → ℝ) (a b : ℝ) (B : ℝ≥0) (hB : 0 < B)
    (hband : ∀ s, s ≤ B → F s ∈ Icc a b)
    (hpre : ∀ t, 0 < t → t ≤ B →
      Y t ∈ Icc a b ∧ Tendsto F (𝓝[<] t) (nhds (Y t)))
    (w : ℝ → ℝ) (hw : ContinuousOn w (Icc a b))
    (k : ℝ≥0 → ℝ) (hk : Measurable k)
    (L : ℝ) (hL : 0 ≤ L) (hkb : ∀ t, ‖k t‖ ≤ L) :
    let A : ℝ≥0 → ℝ := fun t =>
      if t ≤ B ∧ Y t ∈ Icc a b then k t * w (Y t) else 0
    Integrable A μ ∧ Tendsto (fun n : ℕ =>
      let u : ℕ → ℝ≥0 := fun i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
      ∫ t, (∑ i ∈ Finset.range (n + 1), (Ioc (u i) (u (i + 1))).indicator
        (fun r => k r * w (F (u i)))) t ∂μ)
      atTop (nhds (∫ t, A t ∂μ)) := by
  classical
  intro A
  let u : ℕ → ℕ → ℝ≥0 := fun n i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
  let G : ℕ → ℝ≥0 → ℝ := fun n =>
    ∑ i ∈ Finset.range (n + 1), (Ioc (u n i) (u n (i + 1))).indicator
      (fun t => k t * w (F (u n i)))
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hw
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ (hband 0 zero_le))
  have hub (n i : ℕ) (hi : i < n + 1) : u n (i + 1) ≤ B := by
    dsimp [u]
    apply (div_le_iff₀ (by positivity)).mpr
    gcongr
    exact_mod_cast (show i ≤ n from by omega)
  have hGmeas (n : ℕ) : AEStronglyMeasurable (G n) μ := by
    apply Measurable.aestronglyMeasurable
    convert (Finset.measurable_sum (Finset.range (n + 1)) (fun i _ =>
      (hk.mul_const (w (F (u n i)))).indicator
        (show MeasurableSet (Ioc (u n i) (u n (i + 1))) from measurableSet_Ioc))) using 1
    funext t
    simp only [G, Finset.sum_apply]
  have hinside (t : ℝ≥0) (ht : 0 < t) (htB : t ≤ B) :
      (∀ n, ‖G n t‖ ≤ L * M) ∧
      Tendsto (fun n => G n t) atTop (nhds (k t * w (Y t))) := by
    exact avram_chat24_uniform_step_pointwise_core F Y a b B hB hband hpre w hw k L M hL hkb hM t ht htB
  have houtside (n : ℕ) (t : ℝ≥0) (ht : ¬ (0 < t ∧ t ≤ B)) : G n t = 0 := by
    simp only [G, Finset.sum_apply, Set.indicator_apply, mem_Ioc]
    apply Finset.sum_eq_zero
    intro i hi
    have hn : ¬ (u n i < t ∧ t ≤ u n (i + 1)) := by
      intro hh
      exact ht ⟨lt_of_le_of_lt zero_le hh.1,
        hh.2.trans (hub n i (Finset.mem_range.mp hi))⟩
    simp only [if_neg hn]
  have hbound (n : ℕ) : ∀ᵐ t ∂μ, ‖G n t‖ ≤ L * M := by
    apply Filter.Eventually.of_forall
    intro t
    by_cases ht : 0 < t ∧ t ≤ B
    · exact (hinside t ht.1 ht.2).1 n
    · rw [houtside n t ht, norm_zero]
      exact mul_nonneg hL hM0
  have hae0 : ∀ᵐ t ∂μ, t ≠ 0 := by rw [ae_iff]; simpa using hzero
  have hlim : ∀ᵐ t ∂μ, Tendsto (fun n => G n t) atTop (nhds (A t)) := by
    filter_upwards [hae0] with t ht0
    have ht : 0 < t := pos_iff_ne_zero.mpr ht0
    by_cases htB : t ≤ B
    · have hcond : t ≤ B ∧ Y t ∈ Icc a b := ⟨htB, (hpre t ht htB).1⟩
      simpa only [A, if_pos hcond] using (hinside t ht htB).2
    · have hcond : ¬ (t ≤ B ∧ Y t ∈ Icc a b) := fun h => htB h.1
      have hz (n : ℕ) := houtside n t (fun h => htB h.2)
      simpa only [hz, A, if_neg hcond] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  have hdom : Integrable (fun _ : ℝ≥0 => L * M) μ := integrable_const _
  have hAI : Integrable A μ :=
    ⟨aestronglyMeasurable_of_tendsto_ae atTop hGmeas hlim,
      hasFiniteIntegral_of_dominated_convergence hdom.2 hbound hlim⟩
  exact ⟨hAI, tendsto_integral_of_dominated_convergence
    (fun _ : ℝ≥0 => L * M) hGmeas hdom hbound hlim⟩

end
