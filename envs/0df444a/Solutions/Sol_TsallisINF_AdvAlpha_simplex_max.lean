-- Prove2me | solution 1 for TsallisINF.AdvAlpha.simplex_max
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T07:42:25.909294+00:00
-- url     : https://prove2.me/submissions/f2140bc4-ea6f-4b5a-a7d6-d2aafc1e6ab6

import Mathlib
set_option autoImplicit false

theorem solution {K : ℕ} (hK : 0 < K) (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    IsGreatest ((fun z : Fin K → ℝ => ∑ i, z i ^ (1 - α)) '' stdSimplex ℝ (Fin K))
      ((K : ℝ) ^ α) := by
  obtain ⟨h0, h1⟩ := hα
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  constructor
  · refine ⟨fun _ => 1 / (K : ℝ), ⟨fun _ => by positivity, ?_⟩, ?_⟩
    · simp [Finset.sum_const, Finset.card_univ]
      field_simp
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Real.div_rpow zero_le_one hKpos.le, Real.one_rpow]
      have hne : (K : ℝ) ^ (1 - α) ≠ 0 := (Real.rpow_pos_of_pos hKpos _).ne'
      have h2 : (K : ℝ) = (K : ℝ) ^ (1 - α) * (K : ℝ) ^ α := by
        rw [← Real.rpow_add hKpos]; simp
      calc (K : ℝ) * (1 / (K : ℝ) ^ (1 - α))
          = (K : ℝ) ^ (1 - α) * (K : ℝ) ^ α * (1 / (K : ℝ) ^ (1 - α)) := by rw [← h2]
        _ = (K : ℝ) ^ α := by field_simp
  · rintro _ ⟨z, ⟨hz, hs⟩, rfl⟩
    have hpq : (α⁻¹).HolderConjugate ((1 - α)⁻¹) :=
      Real.HolderConjugate.inv_one_sub_inv h0 h1
    have key := Real.inner_le_Lp_mul_Lq (Finset.univ : Finset (Fin K)) (fun _ => (1 : ℝ))
      (fun i => z i ^ (1 - α)) hpq
    simp only [one_mul, abs_one, Real.one_rpow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, one_div, inv_inv] at key
    have hsum : ∑ i, |z i ^ (1 - α)| ^ (1 - α)⁻¹ = 1 := by
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hs
      have hzi : 0 ≤ z i := hz i
      rw [abs_of_nonneg (Real.rpow_nonneg hzi _), ← Real.rpow_mul hzi]
      have : (1 - α) * (1 - α)⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
      rw [this, Real.rpow_one]
    rw [hsum, Real.one_rpow, mul_one] at key
    exact key
