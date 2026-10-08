-- Prove2me | solution 1 for VarianceRegularization.Localized.robust_variance_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T04:04:52.815785+00:00
-- url     : https://prove2.me/submissions/56c2d6d0-9aa5-4fd4-9a40-69b4fe27d309

import Mathlib
import Definitions.Def_UnderstandingML_Rademacher
import Definitions.Def_VarianceRegularization_Localized_RobustRisk
import Definitions.Def_VarianceRegularization_Localized_LocalizedComplexity

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace P2e8d876bAux

open VarianceRegularization.Expansion

noncomputable def empMean {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, z i

noncomputable def sampleVar {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, z i ^ 2 - empMean z ^ 2

/-- sum of centered values is zero -/
lemma sum_centered {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) :
    ∑ i, (z i - empMean z) = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, empMean]
  field_simp
  ring

lemma sum_centered_sq {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) :
    ∑ i, (z i - empMean z) ^ 2 = (n : ℝ) * sampleVar z := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 : ∑ i, (z i - empMean z) ^ 2
      = ∑ i, z i ^ 2 - 2 * empMean z * ∑ i, z i + n * empMean z ^ 2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    congr 1
    · congr 1
      apply Finset.sum_congr rfl; intro i _; ring
  have hs : ∑ i, z i = n * empMean z := by
    simp only [empMean]; field_simp
  rw [h1, hs, sampleVar]
  field_simp
  ring

lemma sampleVar_nonneg {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) : 0 ≤ sampleVar z := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have := sum_centered_sq hn z
  have h0 : 0 ≤ ∑ i, (z i - empMean z) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  rw [this] at h0
  exact nonneg_of_mul_nonneg_right (by linarith) hn'

lemma upper_each {n : ℕ} (hn : 0 < n) (ρ : ℝ) (z : Fin n → ℝ) (p : Fin n → ℝ)
    (hp : p ∈ chiSqBall n ρ) :
    ∑ i, p i * z i ≤ empMean z + Real.sqrt (2 * ρ / n * sampleVar z) := by
  obtain ⟨_, hsum, hchi⟩ := hp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set m := empMean z
  set u : Fin n → ℝ := fun i => z i - m
  set q : Fin n → ℝ := fun i => (n : ℝ) * p i - 1
  have hu0 : ∑ i, u i = 0 := sum_centered hn z
  have hu2 : ∑ i, u i ^ 2 = n * sampleVar z := sum_centered_sq hn z
  have key : ∑ i, p i * z i - m = (n : ℝ)⁻¹ * ∑ i, q i * u i := by
    have e1 : ∑ i, q i * u i = n * ∑ i, p i * z i - n * m * ∑ i, p i - ∑ i, u i := by
      simp only [q, u, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [e1, hsum, hu0]
    field_simp
    ring
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ q u
  have hq2 : ∑ i, q i ^ 2 ≤ 2 * ρ := by simp only [q]; linarith
  have hV := sampleVar_nonneg hn z
  have hsq : (∑ i, p i * z i - m) ^ 2 ≤ 2 * ρ / n * sampleVar z := by
    rw [key, mul_pow]
    have : (∑ i, q i * u i) ^ 2 ≤ 2 * ρ * (n * sampleVar z) := by
      calc _ ≤ (∑ i, q i ^ 2) * ∑ i, u i ^ 2 := cs
        _ ≤ 2 * ρ * (n * sampleVar z) := by
          rw [hu2]; exact mul_le_mul_of_nonneg_right hq2 (by positivity)
    calc ((n : ℝ)⁻¹) ^ 2 * (∑ i, q i * u i) ^ 2 ≤ ((n : ℝ)⁻¹) ^ 2 * (2 * ρ * (n * sampleVar z)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * ρ / n * sampleVar z := by field_simp
  have := Real.abs_le_sqrt hsq
  have := le_abs_self (∑ i, p i * z i - m)
  linarith

lemma feasible {n : ℕ} (hn : 0 < n) (ρ : ℝ) (M0 M1 : ℝ) (z : Fin n → ℝ)
    (hz : ∀ i, z i ∈ Set.Icc M0 M1) (t : ℝ) (ht : 0 ≤ t) (htM : t * (M1 - M0) ≤ 1)
    (htV : t ^ 2 * (n * sampleVar z) ≤ 2 * ρ) :
    (fun i => ((n : ℝ))⁻¹ * (1 + t * (z i - empMean z))) ∈ chiSqBall n ρ ∧
    ∑ i, ((n : ℝ))⁻¹ * (1 + t * (z i - empMean z)) * z i = empMean z + t * sampleVar z := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := hn'.ne'
  set m := empMean z
  have hu0 : ∑ i, (z i - m) = 0 := sum_centered hn z
  have hu2 : ∑ i, (z i - m) ^ 2 = n * sampleVar z := sum_centered_sq hn z
  have hmle : m ≤ M1 := by
    have : ∑ i, z i ≤ ∑ _i : Fin n, M1 := Finset.sum_le_sum (fun i _ => (hz i).2)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    simp only [m, empMean]
    rw [inv_mul_le_iff₀ hn']; linarith
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro i
    have h1 : M0 - m ≤ z i - m := by linarith [(hz i).1]
    have h2 : 0 ≤ 1 + t * (z i - m) := by nlinarith
    positivity
  · rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, hu0]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp; ring
  · have : ∀ i, ((n : ℝ) * ((n : ℝ)⁻¹ * (1 + t * (z i - m))) - 1) ^ 2 = t ^ 2 * (z i - m) ^ 2 := by
      intro i; field_simp; ring
    simp only [this, ← Finset.mul_sum, hu2]
    linarith
  · have e : ∀ i, (n : ℝ)⁻¹ * (1 + t * (z i - m)) * z i
        = (n : ℝ)⁻¹ * z i + (n : ℝ)⁻¹ * t * (z i - m) ^ 2 + (n : ℝ)⁻¹ * t * m * (z i - m) := by
      intro i; ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, hu2, hu0]
    simp only [m, empMean]
    field_simp
    ring

lemma lower_of {n : ℕ} (hn : 0 < n) (ρ : ℝ) (_hρ : 0 ≤ ρ) (M0 M1 : ℝ) (z : Fin n → ℝ)
    (hz : ∀ i, z i ∈ Set.Icc M0 M1) (t : ℝ) (ht : 0 ≤ t) (htM : t * (M1 - M0) ≤ 1)
    (htV : t ^ 2 * (n * sampleVar z) ≤ 2 * ρ) :
    empMean z + t * sampleVar z ≤ robustSup n ρ z := by
  obtain ⟨hmem, hval⟩ := feasible hn ρ M0 M1 z hz t ht htM htV
  unfold robustSup
  apply le_csSup
  · refine ⟨empMean z + Real.sqrt (2 * ρ / n * sampleVar z), ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact upper_each hn ρ z p hp
  · exact ⟨_, hmem, hval⟩

end P2e8d876bAux

namespace P2e8d876bAux

theorem core (n : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 ≤ ρ) (M0 M1 : ℝ)
    (hM : M0 ≤ M1) (z : Fin n → ℝ) (hz : ∀ i, z i ∈ Set.Icc M0 M1) :
    max (Real.sqrt (2 * ρ / n * sampleVar z) - 2 * (M1 - M0) * ρ / n) 0
        ≤ VarianceRegularization.Expansion.robustSup n ρ z - P2e8d876bAux.empMean z ∧
      VarianceRegularization.Expansion.robustSup n ρ z - P2e8d876bAux.empMean z ≤ Real.sqrt (2 * ρ / n * sampleVar z) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hV := P2e8d876bAux.sampleVar_nonneg hn z
  set V := sampleVar z with hVdef
  set A := Real.sqrt (2 * ρ / n * V) with hAdef
  set M := M1 - M0 with hMdef
  have hM0 : 0 ≤ M := by simp only [M]; linarith
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hA2 : A ^ 2 = 2 * ρ / n * V := Real.sq_sqrt (by positivity)
  -- nonemptiness / t = 0
  have h0 : P2e8d876bAux.empMean z ≤ VarianceRegularization.Expansion.robustSup n ρ z := by
    have := P2e8d876bAux.lower_of hn ρ hρ M0 M1 z hz 0 le_rfl (by simp) (by simp; linarith)
    simpa using this
  refine ⟨?_, ?_⟩
  · apply max_le _ (by linarith)
    rcases eq_or_lt_of_le hV with hV0 | hVpos
    · -- V = 0
      have : A = 0 := by rw [hAdef, ← hV0]; simp
      rw [this]
      have : 0 ≤ 2 * M * ρ / n := by positivity
      linarith
    · rcases le_or_gt (A * M) V with hAM | hAM
      · -- t = A / V
        have := P2e8d876bAux.lower_of hn ρ hρ M0 M1 z hz (A / V) (by positivity)
          (by rw [div_mul_eq_mul_div, div_le_one hVpos]; exact hAM)
          (by rw [div_pow, hA2]; apply le_of_eq; field_simp; try rw [hVdef])
        rw [div_mul_cancel₀ _ hVpos.ne'] at this
        have : 0 ≤ 2 * M * ρ / n := by positivity
        linarith
      · -- t = 1 / M
        have hMpos : 0 < M := by
          rcases eq_or_lt_of_le hM0 with h | h
          · rw [← h] at hAM; simp at hAM; linarith
          · exact h
        have hVlt : V < 2 * ρ / n * M ^ 2 := by
          have : V ^ 2 < (A * M) ^ 2 := by nlinarith
          rw [mul_pow, hA2] at this
          nlinarith
        have := P2e8d876bAux.lower_of hn ρ hρ M0 M1 z hz (1 / M) (by positivity)
          (by rw [div_mul_cancel₀ _ hMpos.ne'])
          (by
            rw [div_pow, one_pow]
            rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
            have : (n : ℝ) * V < n * (2 * ρ / n * M ^ 2) := mul_lt_mul_of_pos_left hVlt hn'
            have e : (n : ℝ) * (2 * ρ / n * M ^ 2) = 2 * ρ * M ^ 2 := by field_simp
            linarith)
        -- need V/M ≥ A - 2Mρ/n
        have hB : 2 * M * ρ / n = M * (A ^ 2 / V) := by
          rw [hA2]; field_simp
        have goal : A - M * (A ^ 2 / V) ≤ 1 / M * V := by
          rw [show 1 / M * V = V / M by ring]
          rw [div_eq_mul_inv, div_eq_mul_inv]
          have hVi : V * V⁻¹ = 1 := mul_inv_cancel₀ hVpos.ne'
          have hMi : M * M⁻¹ = 1 := mul_inv_cancel₀ hMpos.ne'
          have hVi0 : 0 < V⁻¹ := inv_pos.mpr hVpos
          have hMi0 : 0 < M⁻¹ := inv_pos.mpr hMpos
          -- (V - A M)^2 + A M V ... multiply by V⁻¹ M⁻¹
          have hq : 0 ≤ (V - A * M) ^ 2 + A * M * V := by positivity
          have : A - M * (A ^ 2 * V⁻¹) - V * M⁻¹ = -(V⁻¹ * M⁻¹) * ((V - A * M) ^ 2 + A * M * V) := by
            field_simp; ring
          nlinarith [mul_nonneg (mul_pos hVi0 hMi0).le hq]
        linarith
  · have h := Real.sqrt_nonneg (2 * ρ / n * V)
    unfold VarianceRegularization.Expansion.robustSup
    have := csSup_le (s := (fun p : Fin n → ℝ => ∑ i, p i * z i) '' VarianceRegularization.Expansion.chiSqBall n ρ)
      (a := P2e8d876bAux.empMean z + A) ?_ ?_
    · linarith
    · obtain ⟨hmem, _⟩ := P2e8d876bAux.feasible hn ρ M0 M1 z hz 0 le_rfl (by simp) (by simp; linarith)
      exact ⟨_, _, hmem, rfl⟩
    · rintro _ ⟨p, hp, rfl⟩
      exact P2e8d876bAux.upper_each hn ρ z p hp

lemma empMean_eq {n : ℕ} (z : Fin n → ℝ) :
    VarianceRegularization.Localized.empMean z (fun x => x) =
      P2e8d876bAux.empMean z := by
  simp [VarianceRegularization.Localized.empMean, P2e8d876bAux.empMean]

lemma empVar_eq {n : ℕ} (z : Fin n → ℝ) :
    VarianceRegularization.Localized.empVar z (fun x => x) =
      P2e8d876bAux.sampleVar z := by
  simp [VarianceRegularization.Localized.empVar, P2e8d876bAux.sampleVar, empMean_eq]

end P2e8d876bAux

open VarianceRegularization.Localized in
theorem solution (n : ℕ) (hn : 0 < n) (M0 M1 ρ : ℝ) (hρ : 0 ≤ ρ)
    (z : Fin n → ℝ) (hz : ∀ i, z i ∈ Set.Icc M0 M1) :
    max (Real.sqrt (2 * ρ / n * empVar z (fun x => x)) - 2 * (M1 - M0) * ρ / n) 0
        ≤ VarianceRegularization.Expansion.robustSup n ρ z - empMean z (fun x => x) ∧
      VarianceRegularization.Expansion.robustSup n ρ z - empMean z (fun x => x)
        ≤ Real.sqrt (2 * ρ / n * empVar z (fun x => x)) := by
  have hM : M0 ≤ M1 := (hz ⟨0, hn⟩).1.trans (hz ⟨0, hn⟩).2
  rw [P2e8d876bAux.empMean_eq, P2e8d876bAux.empVar_eq]
  exact P2e8d876bAux.core n hn ρ hρ M0 M1 hM z hz
