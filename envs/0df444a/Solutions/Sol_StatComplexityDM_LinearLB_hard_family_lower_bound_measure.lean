-- Prove2me | solution 1 for StatComplexityDM.LinearLB.hard_family_lower_bound_measure
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:49:03.075591+00:00
-- url     : https://prove2.me/submissions/8dad51eb-594c-451d-91e3-44076c195af3

import Mathlib

open MeasureTheory

theorem solution {X : Type*} [MeasurableSpace X]
    (p : ProbabilityMeasure X) (N : ℕ) (hN : 2 ≤ N) (α β δ γ : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 < γ)
    (g D u v : Fin N → X → ℝ)
    (hg : ∀ i, Integrable (g i) (p : Measure X)) (hD : ∀ i, Integrable (D i) (p : Measure X))
    (hu : ∀ i, Integrable (u i) (p : Measure X)) (hv : ∀ i, Integrable (v i) (p : Measure X))
    (hreg : ∀ i x, α * (1 - u i x) ≤ g i x)
    (hinfo : ∀ i x, D i x ≤ β * v i x + δ)
    (hu_sum : ∀ x, ∑ i, u i x ≤ (N : ℝ) / 2)
    (hv_sum : ∀ x, ∑ i, v i x ≤ 1) :
    ∃ i : Fin N, α / 2 - γ * (β / N + δ) ≤ ∫ x, (g i x - γ * D i x) ∂(p : Measure X) := by
  set c := α / 2 - γ * (β / N + δ) with hc
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hpt : ∀ x, (N : ℝ) * c ≤ ∑ i, (g i x - γ * D i x) := by
    intro x
    have h1 : ∑ i, α * (1 - u i x) ≤ ∑ i, g i x := Finset.sum_le_sum (fun i _ => hreg i x)
    have h2 : ∑ i, D i x ≤ ∑ i, (β * v i x + δ) := Finset.sum_le_sum (fun i _ => hinfo i x)
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at h1
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at h2
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    have e1 : (N : ℝ) * c = N * α / 2 - γ * β - N * γ * δ := by
      rw [hc]; field_simp; ring
    rw [e1]
    have a1 := mul_le_mul_of_nonneg_left (hu_sum x) hα
    have a2 := mul_le_mul_of_nonneg_left (hv_sum x) (mul_nonneg hγ.le hβ)
    have a3 := mul_le_mul_of_nonneg_left h2 hγ.le
    nlinarith
  have hint : ∀ i, Integrable (fun x => g i x - γ * D i x) (p : Measure X) :=
    fun i => (hg i).sub ((hD i).const_mul γ)
  have hsum : (N : ℝ) * c ≤ ∑ i, ∫ x, (g i x - γ * D i x) ∂(p : Measure X) := by
    rw [← integral_finset_sum _ (fun i _ => hint i)]
    have := integral_mono (integrable_const ((N : ℝ) * c))
      (integrable_finset_sum _ (fun i _ => hint i)) hpt
    simpa using this
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hsum' : ∑ _i : Fin N, c ≤ ∑ i, ∫ x, (g i x - γ * D i x) ∂(p : Measure X) := by
    simpa using hsum
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le hne hsum'
  exact ⟨i, hi⟩
