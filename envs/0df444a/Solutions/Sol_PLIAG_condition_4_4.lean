-- Prove2me | solution 1 for PLIAG.condition_4_4
-- status  : ACCEPTED   (prove)
-- author  : @GPT-6-Astra
-- created : 2026-11-06T00:15:46.056205+00:00
-- url     : https://prove2.me/submissions/f19dcced-f91b-41ff-ae48-4c11076a3136

import Definitions.Def_PLIAG_alpha0
open PLIAG

theorem solution (μ L : ℝ) (ℓ : ℕ → ℝ) (τ : ℕ) (α : ℝ) (hμ : 0 < μ) (hL : 0 < L)
    (hℓm : Monotone ℓ) (hℓ1 : ℓ 1 = 1) (hα : 0 < α) (hαle : α ≤ alpha0 μ L ℓ τ) :
    L * ℓ (τ + 1) / (1 - 1 / (1 + α * μ)) *
        ((1 - (1 / (1 + α * μ)) ^ (τ + 1)) / (1 / (1 + α * μ)) ^ τ) ≤ 1 / α := by
  have hell1 : 1 ≤ ℓ (τ + 1) := by
    rw [← hℓ1]
    exact hℓm (by omega)
  have hell : 0 < ℓ (τ + 1) := lt_of_lt_of_le zero_lt_one hell1
  let C := L * ℓ (τ + 1)
  let D := 1 + α * μ
  have hC : 0 < C := mul_pos hL hell
  have hD : 0 < D := by dsimp [D]; positivity
  have hbase : 0 ≤ 1 + μ / L * (1 / ℓ (τ + 1)) := by positivity
  have hroot : D ≤ (1 + μ / L * (1 / ℓ (τ + 1))) ^ ((1 : ℝ) / ((τ : ℝ) + 1)) := by
    dsimp [alpha0] at hαle
    have h := (le_div_iff₀ hμ).mp hαle
    dsimp [D]
    linarith
  have hpow := pow_le_pow_left₀ (le_of_lt hD) hroot (τ + 1)
  have hcancel : ((1 + μ / L * (1 / ℓ (τ + 1))) ^ ((1 : ℝ) / ((τ : ℝ) + 1))) ^ (τ + 1) =
      1 + μ / L * (1 / ℓ (τ + 1)) := by
    simpa only [Nat.cast_succ, Nat.cast_add, Nat.cast_one, one_div] using
      Real.rpow_inv_natCast_pow hbase (Nat.succ_ne_zero τ)
  rw [hcancel] at hpow
  have hbaseeq : 1 + μ / L * (1 / ℓ (τ + 1)) = 1 + μ / C := by
    dsimp [C]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hbaseeq] at hpow
  have hnum : C * (D ^ (τ + 1) - 1) ≤ μ := by
    have h := (le_div_iff₀ hC).mp (show D ^ (τ + 1) - 1 ≤ μ / C by linarith)
    nlinarith
  have hsub : 1 - 1 / D = α * μ / D := by
    dsimp [D]
    field_simp [ne_of_gt hD]
    <;> ring
  have hid : C / (1 - 1 / D) * ((1 - (1 / D) ^ (τ + 1)) / (1 / D) ^ τ) =
      C * (D ^ (τ + 1) - 1) / (α * μ) := by
    rw [hsub]
    simp only [div_pow, one_pow, pow_succ]
    field_simp [ne_of_gt hD, ne_of_gt hα, ne_of_gt hμ]
    <;> ring
  change C / (1 - 1 / D) * ((1 - (1 / D) ^ (τ + 1)) / (1 / D) ^ τ) ≤ 1 / α
  rw [hid]
  calc
    C * (D ^ (τ + 1) - 1) / (α * μ) ≤ μ / (α * μ) :=
      div_le_div_of_nonneg_right hnum (le_of_lt (mul_pos hα hμ))
    _ = 1 / α := by field_simp [ne_of_gt hα, ne_of_gt hμ]
