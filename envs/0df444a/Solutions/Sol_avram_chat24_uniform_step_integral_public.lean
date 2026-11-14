-- Prove2me | solution 1 for avram_chat24_uniform_step_integral_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:54:29.530114+00:00
-- url     : https://prove2.me/submissions/ba22a6d1-ac4a-4b42-bfc9-edf38b7054b1

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem solution
    (μ : Measure ℝ≥0) (B : ℝ≥0) (k E C : ℝ≥0 → ℝ)
    (hkI : Integrable k μ)
    (hcell : ∀ s t : ℝ≥0, s ≤ t → t ≤ B →
      (∫ r in Ioc s t, k r ∂μ) = E t - E s) (n : ℕ) :
    let u : ℕ → ℝ≥0 := fun i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    (∫ t, (∑ i ∈ Finset.range (n + 1), (Ioc (u i) (u (i + 1))).indicator
      (fun r => k r * C (u i))) t ∂μ) =
      ∑ i ∈ Finset.range (n + 1), (E (u (i + 1)) - E (u i)) * C (u i) := by
  classical
  intro u
  have hub (i : ℕ) (hi : i < n + 1) : u (i + 1) ≤ B := by
    dsimp [u]
    apply (div_le_iff₀ (by positivity)).mpr
    gcongr
    exact_mod_cast (show i ≤ n from by omega)
  have huk (i : ℕ) : u i ≤ u (i + 1) := by
    dsimp [u]
    gcongr
    exact_mod_cast (show i ≤ i + 1 from by omega)
  simp only [Finset.sum_apply]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_indicator measurableSet_Ioc, integral_mul_const,
      hcell _ _ (huk i) (hub i (Finset.mem_range.mp hi))]
  · intro i hi
    exact (hkI.mul_const _).indicator measurableSet_Ioc

