-- Prove2me | solution 1 for VolunteerNotify.claim_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:06:20.947993+00:00
-- url     : https://prove2.me/submissions/4095381b-2250-43c0-8b0c-208d07c5e0d7

import Mathlib

theorem solution (n : ℕ) (hn : 1 ≤ n) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) (x p : Fin n → ℝ)
    (hx : ∀ v, x v ∈ Set.Icc (0 : ℝ) 1) (hp : ∀ v, p v ∈ Set.Icc (0 : ℝ) 1)
    (hsum : c = ∑ v, x v * p v) : ∏ v, (1 - x v * p v) ≤ (1 - c / n) ^ n := by
  have hn' : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hz : ∀ v, 0 ≤ 1 - x v * p v := by
    intro v
    obtain ⟨hx0, hx1⟩ := hx v
    obtain ⟨hp0, hp1⟩ := hp v
    have := mul_le_one₀ hx1 hp0 hp1
    linarith
  have hw : ∑ _v : Fin n, (n : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ hn'.ne'
  have amgm : ∏ v, (1 - x v * p v) ^ ((n : ℝ)⁻¹) ≤ ∑ v, (n : ℝ)⁻¹ * (1 - x v * p v) :=
    Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => (n : ℝ)⁻¹)
      (fun v => 1 - x v * p v) (fun _ _ => inv_nonneg.mpr hn'.le) hw (fun i _ => hz i)
  have hrhs : ∑ v, (n : ℝ)⁻¹ * (1 - x v * p v) = 1 - c / n := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← hsum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, mul_sub, inv_mul_cancel₀ hn'.ne', div_eq_inv_mul]
  rw [hrhs, Real.finsetProd_rpow _ _ (fun i _ => hz i)] at amgm
  have hP : 0 ≤ ∏ v, (1 - x v * p v) := Finset.prod_nonneg (fun i _ => hz i)
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hP _) amgm n
  rwa [Real.rpow_inv_natCast_pow hP (by omega : n ≠ 0)] at hpow
