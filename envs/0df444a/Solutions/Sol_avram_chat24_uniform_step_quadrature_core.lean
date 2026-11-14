-- Prove2me | solution 1 for avram_chat24_uniform_step_quadrature_core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:40:31.613923+00:00
-- url     : https://prove2.me/submissions/a85a1476-f42d-4ab5-bdde-7ae7ecc1b63f

import Mathlib
import Theorems.Thm_avram_chat24_uniform_step_DCT_public
import Theorems.Thm_avram_chat24_uniform_step_integral_public
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
    (k E : ℝ≥0 → ℝ) (hk : Measurable k)
    (L : ℝ) (hL : 0 ≤ L) (hkb : ∀ t, ‖k t‖ ≤ L)
    (hcell : ∀ s t : ℝ≥0, s ≤ t → t ≤ B →
      (∫ r in Ioc s t, k r ∂μ) = E t - E s) :
    let A : ℝ≥0 → ℝ := fun t =>
      if t ≤ B ∧ Y t ∈ Icc a b then k t * w (Y t) else 0
    Integrable A μ ∧ Tendsto (fun n : ℕ =>
      let u : ℕ → ℝ≥0 := fun i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
      ∑ i ∈ Finset.range (n + 1), (E (u (i + 1)) - E (u i)) * w (F (u i)))
      atTop (nhds (∫ t, A t ∂μ)) := by
  classical
  intro A
  have hkI : Integrable k μ := (integrable_const L).mono' hk.aestronglyMeasurable
    (Filter.Eventually.of_forall hkb)
  obtain ⟨hAI, hlim⟩ := avram_chat24_uniform_step_DCT_public μ hzero
    F Y a b B hB hband hpre w hw k hk L hL hkb
  have hsum (n : ℕ) :
      (let u : ℕ → ℝ≥0 := fun i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
       ∫ t, (∑ i ∈ Finset.range (n + 1), (Ioc (u i) (u (i + 1))).indicator
         (fun r => k r * w (F (u i)))) t ∂μ) =
      (let u : ℕ → ℝ≥0 := fun i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
       ∑ i ∈ Finset.range (n + 1), (E (u (i + 1)) - E (u i)) * w (F (u i))) :=
    avram_chat24_uniform_step_integral_public μ B k E (fun s => w (F s)) hkI hcell n
  refine ⟨hAI, ?_⟩
  simpa only [hsum] using hlim
end
