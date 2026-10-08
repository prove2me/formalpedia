-- Prove2me | solution 1 for VarianceRegularization.FastRates.robust_sup_sub_mean_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T08:34:04.533132+00:00
-- url     : https://prove2.me/submissions/ff83a2ac-5a0e-4da3-8180-93518ea5bb5e

import Mathlib
import Definitions.Def_VarianceRegularization_FastRates_RobustRisk

set_option autoImplicit false

open VarianceRegularization.Expansion in
lemma vr918_elem_bound (n : ℕ) (hn : 0 < n) (ρ : ℝ) (z : Fin n → ℝ) (p : Fin n → ℝ)
    (hp : p ∈ chiSqBall n ρ) :
    (∑ i, p i * z i) ≤ empMean z +
      Real.sqrt (2 * ρ / n * VarianceRegularization.FastRates.empVar z) := by
  obtain ⟨-, hp1, hρ⟩ := hp
  set n' : ℝ := (n : ℝ) with hn'def
  have hn' : 0 < n' := by positivity
  set m := empMean z with hm
  set V := VarianceRegularization.FastRates.empVar z with hV
  set S := ∑ i, p i * z i with hS
  have hz : ∑ i, z i = n' * m := by
    rw [hm, empMean]; field_simp; try rfl
  have hq : ∑ i, (n' * p i - 1) * (z i - m) = n' * (S - m) := by
    have h : ∀ i, (n' * p i - 1) * (z i - m) = n' * (p i * z i) - (n' * m) * p i - z i + m := by
      intro i; ring
    rw [Finset.sum_congr rfl (fun i _ => h i)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hp1, hz, ← hS]; ring
  have hw : ∑ i, (z i - m) ^ 2 = n' * V := by
    have h : ∀ i, (z i - m) ^ 2 = z i ^ 2 - (2 * m) * z i + m ^ 2 := by intro i; ring
    rw [Finset.sum_congr rfl (fun i _ => h i)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hz, hV, VarianceRegularization.FastRates.empVar, ← hm, ← hn'def]
    field_simp
    ring
  have hq2 : ∑ i, (n' * p i - 1) ^ 2 ≤ 2 * ρ := by linarith
  have hw0 : 0 ≤ ∑ i, (z i - m) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => n' * p i - 1) (fun i => z i - m)
  rw [hq] at hcs
  have key : n' ^ 2 * (S - m) ^ 2 ≤ n' ^ 2 * (2 * ρ / n' * V) := by
    have e : n' ^ 2 * (2 * ρ / n' * V) = 2 * ρ * (n' * V) := by field_simp
    rw [e, ← hw]
    calc n' ^ 2 * (S - m) ^ 2 = (n' * (S - m)) ^ 2 := by ring
      _ ≤ _ := hcs
      _ ≤ 2 * ρ * ∑ i, (z i - m) ^ 2 := mul_le_mul_of_nonneg_right hq2 hw0
  have key2 : (S - m) ^ 2 ≤ 2 * ρ / n' * V := le_of_mul_le_mul_left key (by positivity)
  have := Real.abs_le_sqrt key2
  linarith [le_abs_self (S - m)]

open VarianceRegularization.FastRates in
theorem solution (n : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 ≤ ρ) (z : Fin n → ℝ) :
    VarianceRegularization.Expansion.robustSup n ρ z - VarianceRegularization.Expansion.empMean z ≤ Real.sqrt (2 * ρ / n * empVar z) := by
  have hne : ((fun p : Fin n → ℝ => ∑ i, p i * z i) ''
      VarianceRegularization.Expansion.chiSqBall n ρ).Nonempty := by
    refine ⟨_, (fun _ => (1 : ℝ) / n), ?_, rfl⟩
    have hn' : (n : ℝ) ≠ 0 := by positivity
    refine ⟨fun _ => by positivity, ?_, ?_⟩
    · simp [Finset.sum_const, Finset.card_univ]; field_simp
    · have h0 : (n : ℝ) * (1 / n) - 1 = 0 := by rw [mul_one_div_cancel hn']; ring
      show (1 / 2 : ℝ) * ∑ i : Fin n, ((n : ℝ) * (1 / n) - 1) ^ 2 ≤ ρ
      rw [h0]; simpa using hρ
  rw [sub_le_iff_le_add, add_comm]
  unfold VarianceRegularization.Expansion.robustSup
  apply csSup_le hne
  rintro _ ⟨p, hp, rfl⟩
  exact vr918_elem_bound n hn ρ z p hp
