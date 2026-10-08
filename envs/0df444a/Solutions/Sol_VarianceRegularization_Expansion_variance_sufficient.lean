-- Prove2me | solution 1 for VarianceRegularization.Expansion.variance_sufficient
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T02:56:31.841656+00:00
-- url     : https://prove2.me/submissions/fe0ac45d-604e-4dbd-98bb-3e91be8a1e9a

import Mathlib
import Definitions.Def_VarianceRegularization_Expansion_robustSup
import Definitions.Def_VarianceRegularization_Expansion_empVar

set_option autoImplicit false

namespace VarianceRegularization.Expansion.VSuff2e08

open VarianceRegularization.Expansion

lemma sum_dev {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) :
    ∑ i, (z i - empMean z) = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, empMean]
  field_simp
  ring

lemma sum_sq_dev {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) :
    ∑ i, (z i - empMean z) ^ 2 = n * empVar z := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hm : ∑ i, z i = n * empMean z := by
    simp only [empMean]; field_simp
  have h : ∀ i, (z i - empMean z) ^ 2 = z i ^ 2 - 2 * empMean z * z i + empMean z ^ 2 :=
    fun i => by ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hm, empVar]
  field_simp
  ring

lemma sum_dev_mul {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) :
    ∑ i, (z i - empMean z) * z i = n * empVar z := by
  have h : ∀ i, (z i - empMean z) * z i = (z i - empMean z) ^ 2 + empMean z * (z i - empMean z) :=
    fun i => by ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, sum_dev hn, sum_sq_dev hn]
  ring

lemma mean_mem {n : ℕ} (hn : 0 < n) (M₀ M₁ : ℝ) (z : Fin n → ℝ)
    (hz : ∀ i, z i ∈ Set.Icc M₀ M₁) :
    M₀ ≤ empMean z ∧ empMean z ≤ M₁ := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (n : ℝ) * M₀ ≤ ∑ i, z i := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hz i).1)
    simpa using this
  have h2 : ∑ i, z i ≤ (n : ℝ) * M₁ := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hz i).2)
    simpa using this
  unfold empMean
  constructor
  · rw [le_inv_mul_iff₀ hnpos]; linarith
  · rw [inv_mul_le_iff₀ hnpos]; linarith

theorem main {n : ℕ} (hn : 0 < n) (ρ M₀ M₁ : ℝ)
    (hρ : 0 ≤ ρ) (hM : M₀ ≤ M₁) (z : Fin n → ℝ)
    (hz : ∀ i, z i ∈ Set.Icc M₀ M₁)
    (hvar : 0 < empVar z)
    (h30 : 2 * ρ * (M₁ - M₀) ^ 2 / (n : ℝ) ≤ empVar z) :
    robustSup n ρ z = empMean z + Real.sqrt (2 * ρ / (n : ℝ) * empVar z) := by
  have hsd := sum_dev hn z
  have hssd := sum_sq_dev hn z
  have hsdm := sum_dev_mul hn z
  obtain ⟨hm0, hm1⟩ := mean_mem hn M₀ M₁ z hz
  set m := empMean z with hm_def
  set V := empVar z with hV_def
  set S := Real.sqrt (2 * ρ / (n : ℝ) * V) with hS_def
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS2 : S ^ 2 = 2 * ρ / n * V := Real.sq_sqrt (by positivity)
  unfold robustSup
  apply IsGreatest.csSup_eq
  constructor
  · -- attainment
    set c := S / (n * V) with hc
    have hc0 : 0 ≤ c := by positivity
    have hSM : S * (M₁ - M₀) ≤ V := by
      have hsq : (S * (M₁ - M₀)) ^ 2 ≤ V ^ 2 := by
        have e : (S * (M₁ - M₀)) ^ 2 = 2 * ρ * (M₁ - M₀) ^ 2 / n * V := by
          rw [mul_pow, hS2]; ring
        rw [e]
        calc 2 * ρ * (M₁ - M₀) ^ 2 / n * V ≤ V * V := mul_le_mul_of_nonneg_right h30 hvar.le
          _ = V ^ 2 := (sq V).symm
      have h0 : 0 ≤ S * (M₁ - M₀) := mul_nonneg hS0 (by linarith)
      nlinarith
    have hcM : c * (M₁ - M₀) ≤ 1 / n := by
      rw [hc, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hnpos]
      nlinarith
    refine ⟨fun i => 1 / n + c * (z i - m), ⟨?_, ?_, ?_⟩, ?_⟩
    · intro i
      have hzi := hz i
      have hd : -(z i - m) ≤ M₁ - M₀ := by linarith [hzi.1]
      have := mul_le_mul_of_nonneg_left hd hc0
      show 0 ≤ 1 / (n : ℝ) + c * (z i - m)
      nlinarith
    · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsd, mul_zero, add_zero, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    · have h : ∀ i, ((n : ℝ) * (1 / n + c * (z i - m)) - 1) ^ 2 = (n * c) ^ 2 * (z i - m) ^ 2 := by
        intro i; field_simp; ring
      simp only [h, ← Finset.mul_sum, hssd]
      have key : (n * c) ^ 2 * (n * V) = 2 * ρ := by
        rw [hc]
        have hV0 : V ≠ 0 := hvar.ne'
        have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
        field_simp
        rw [hS2]
        field_simp
      rw [key]; linarith
    · show ∑ i, (1 / (n : ℝ) + c * (z i - m)) * z i = m + S
      have h : ∀ i, (1 / (n : ℝ) + c * (z i - m)) * z i = (1 / n) * z i + c * ((z i - m) * z i) :=
        fun i => by ring
      simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, hsdm]
      rw [hc, hm_def]
      simp only [empMean]
      field_simp
  · -- upper bound
    rintro _ ⟨p, ⟨hp0, hp1, hpc⟩, rfl⟩
    show ∑ i, p i * z i ≤ m + S
    have hid : ∑ i, p i * z i - m = ∑ i, (p i - 1 / n) * (z i - m) := by
      have h : ∀ i, (p i - 1 / n) * (z i - m) = p i * z i - m * p i - (1 / n) * (z i - m) :=
        fun i => by ring
      simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum, hsd, hp1]
      ring
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => p i - 1 / n) (fun i => z i - m)
    have hp2 : ∑ i, (p i - 1 / (n : ℝ)) ^ 2 = (1 / (n : ℝ) ^ 2) * ∑ i, ((n : ℝ) * p i - 1) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
      field_simp
    have hx2 : (∑ i, p i * z i - m) ^ 2 ≤ 2 * ρ / n * V := by
      rw [hid]
      refine hcs.trans ?_
      rw [hp2, hssd]
      have hb : ∑ i, ((n : ℝ) * p i - 1) ^ 2 ≤ 2 * ρ := by linarith
      have : (1 / (n : ℝ) ^ 2 * ∑ i, ((n : ℝ) * p i - 1) ^ 2) * (n * V) ≤
          1 / (n : ℝ) ^ 2 * (2 * ρ) * (n * V) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hb (by positivity)
      refine this.trans (le_of_eq ?_)
      field_simp
    have := Real.abs_le_sqrt hx2
    have := le_abs_self (∑ i, p i * z i - m)
    linarith

end VarianceRegularization.Expansion.VSuff2e08

open VarianceRegularization.Expansion in
theorem solution {n : ℕ} (hn : 0 < n) (ρ M₀ M₁ : ℝ)
    (hρ : 0 ≤ ρ) (hM : M₀ ≤ M₁) (z : Fin n → ℝ)
    (hz : ∀ i, z i ∈ Set.Icc M₀ M₁)
    (hvar : 0 < empVar z)
    (h30 : 2 * ρ * (M₁ - M₀) ^ 2 / (n : ℝ) ≤ empVar z) :
    robustSup n ρ z = empMean z + Real.sqrt (2 * ρ / (n : ℝ) * empVar z) := by
  exact VarianceRegularization.Expansion.VSuff2e08.main hn ρ M₀ M₁ hρ hM z hz hvar h30
