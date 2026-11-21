-- Prove2me | solution 1 for WeightedCongestionBR.lemma_14
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T03:05:43.028108+00:00
-- url     : https://prove2.me/submissions/6a2051c6-e02c-456b-b4a7-ee9b5ad79a17

import Mathlib
import Definitions.Def_WeightedCongestionBR_IsPd
set_option autoImplicit false
open scoped NNReal

namespace Aux_WCBR_l14

/-- Key one-variable inequality: `a (a+x)^k ≤ (1+ε) a^(k+1) + (k(1+1/ε))^k x^(k+1)`. -/
theorem key (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) (a x : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) :
    a * (a + x) ^ k ≤ (1 + ε) * a ^ (k + 1) + ((k : ℝ) * (1 + 1 / ε)) ^ k * x ^ (k + 1) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1ε : (0 : ℝ) < 1 + ε := by linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = ε / (k * (1 + ε)) := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; positivity
  have hs1 : s < 1 := by
    rw [hs, div_lt_one (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hk1 h1ε.le]
  have hkne : (k : ℝ) ≠ 0 := hk0.ne'
  have hu : (k : ℝ) * s = ε / (1 + ε) := by
    rw [hs, mul_div_assoc', mul_div_mul_left _ _ hkne]
  have hinv : 1 / s = (k : ℝ) * (1 + 1 / ε) := by
    rw [hs, one_div_div, mul_div_assoc, add_div, div_self hε.ne', add_comm (1 / ε)]
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = 1 - s := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθ]; linarith
  have hsum : θ + s = 1 := by rw [hθ]; ring
  have hbern : 1 + (k : ℝ) * (-s) ≤ (1 + (-s)) ^ k :=
    one_add_mul_le_pow (by linarith) k
  have hbern' : 1 - ε / (1 + ε) ≤ θ ^ k := by
    have e1 : (1 : ℝ) + (k : ℝ) * (-s) = 1 - ε / (1 + ε) := by rw [← hu]; ring
    have e2 : (1 : ℝ) + (-s) = θ := by rw [hθ]; ring
    rw [e1, e2] at hbern
    exact hbern
  have hid : (1 + ε) * (1 - ε / (1 + ε)) = 1 := by
    rw [mul_sub, mul_one, mul_div_cancel₀ ε h1ε.ne']
    ring
  have hθk : 1 ≤ (1 + ε) * θ ^ k := by
    have := mul_le_mul_of_nonneg_left hbern' h1ε.le
    linarith
  have hconv := (convexOn_pow (𝕜 := ℝ) (k + 1)).2
    (Set.mem_Ici.mpr (div_nonneg ha hθ0.le)) (Set.mem_Ici.mpr (div_nonneg hx hs0.le))
    hθ0.le hs0.le hsum
  simp only [smul_eq_mul] at hconv
  have e3 : θ * (a / θ) + s * (x / s) = a + x := by
    rw [mul_div_cancel₀ a hθ0.ne', mul_div_cancel₀ x hs0.ne']
  rw [e3] at hconv
  have t1 : θ * (a / θ) ^ (k + 1) ≤ (1 + ε) * a ^ (k + 1) := by
    have e4 : θ * (a / θ) ^ (k + 1) = a ^ (k + 1) * (1 / θ ^ k) := by
      rw [div_pow, pow_succ θ k]
      field_simp
    have h5 : 1 / θ ^ k ≤ 1 + ε := by
      rw [div_le_iff₀ (pow_pos hθ0 k)]
      linarith
    rw [e4]
    have := mul_le_mul_of_nonneg_left h5 (pow_nonneg ha (k + 1))
    linarith
  have t2 : s * (x / s) ^ (k + 1) = (1 / s) ^ k * x ^ (k + 1) := by
    rw [div_pow, pow_succ s k, one_div_pow]
    field_simp
  rw [t2, hinv] at hconv
  have h6 : a * (a + x) ^ k ≤ (a + x) ^ (k + 1) := by
    rw [pow_succ]
    have := mul_le_mul_of_nonneg_left (show a ≤ a + x by linarith) (pow_nonneg (by linarith : (0:ℝ) ≤ a + x) k)
    linarith
  linarith

theorem constC (d k : ℕ) (hd : 1 ≤ d) (hkd : k ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ((k : ℝ) * (1 + 1 / ε)) ^ k ≤ (1 + 1 / ε) ^ d * (d : ℝ) ^ d := by
  have h1 : (1 : ℝ) ≤ 1 + 1 / ε := by
    have : 0 ≤ 1 / ε := by positivity
    linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  rw [mul_pow, mul_comm]
  apply mul_le_mul
  · exact pow_le_pow_right₀ h1 hkd
  · calc (k : ℝ) ^ k ≤ (d : ℝ) ^ k :=
          pow_le_pow_left₀ (Nat.cast_nonneg k) (by exact_mod_cast hkd) k
      _ ≤ (d : ℝ) ^ d := pow_le_pow_right₀ hd1 hkd
  · positivity
  · positivity

/-- Monomial version of the inequality. -/
theorem mono (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hkd : k ≤ d) (ε : ℝ) (hε : 0 < ε)
    (x x' y y' z : ℝ) (hx : 0 ≤ x) (hx' : 0 ≤ x') (hy : 0 ≤ y) (hy' : 0 ≤ y') (hz : 0 ≤ z) :
    y * (z + x + y) ^ k ≤
      (1 + ε) * y * (z + x' + y) ^ k + (1 + 1 / ε) ^ d * (d : ℝ) ^ d * x * (z + x + y') ^ k := by
  have hC0 : 0 ≤ (1 + 1 / ε) ^ d * (d : ℝ) ^ d := by positivity
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · simp only [pow_zero, mul_one]
    have := mul_nonneg hε.le hy
    have := mul_nonneg hC0 hx
    linarith
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = (1 + 1 / ε) ^ d * (d : ℝ) ^ d := ⟨_, rfl⟩
  rw [← hC] at hC0 ⊢
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ((k : ℝ) * (1 + 1 / ε)) ^ k := ⟨_, rfl⟩
  have hKC : K ≤ C := by rw [hK, hC]; exact constC d k hd hkd ε hε
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = z + y := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have hya : y ≤ a := by rw [ha]; linarith
  have hA : a ^ k ≤ (z + x' + y) ^ k := pow_le_pow_left₀ ha0 (by rw [ha]; linarith) k
  have hB : x ^ k ≤ (z + x + y') ^ k := pow_le_pow_left₀ hx (by linarith) k
  have e0 : z + x + y = a + x := by rw [ha]; ring
  rw [e0]
  have core : y * (a + x) ^ k ≤ (1 + ε) * y * a ^ k + C * x * x ^ k := by
    by_cases h : (a + x) ^ k ≤ (1 + ε) * a ^ k
    · have := mul_le_mul_of_nonneg_left h hy
      have := mul_nonneg (mul_nonneg hC0 hx) (pow_nonneg hx k)
      have e : (1 + ε) * y * a ^ k = y * ((1 + ε) * a ^ k) := by ring
      linarith
    · push_neg at h
      have e1 := mul_le_mul_of_nonneg_right hya (sub_nonneg.mpr h.le)
      have hkey := key k hk1 ε hε a x ha0 hx
      rw [← hK] at hkey
      have e2 : K * x ^ (k + 1) ≤ C * x * x ^ k := by
        calc K * x ^ (k + 1) ≤ C * x ^ (k + 1) :=
              mul_le_mul_of_nonneg_right hKC (pow_nonneg hx _)
          _ = C * x * x ^ k := by ring
      calc y * (a + x) ^ k
          = y * ((a + x) ^ k - (1 + ε) * a ^ k) + (1 + ε) * y * a ^ k := by ring
        _ ≤ a * ((a + x) ^ k - (1 + ε) * a ^ k) + (1 + ε) * y * a ^ k := by linarith
        _ = a * (a + x) ^ k - (1 + ε) * a ^ (k + 1) + (1 + ε) * y * a ^ k := by ring
        _ ≤ K * x ^ (k + 1) + (1 + ε) * y * a ^ k := by linarith
        _ ≤ (1 + ε) * y * a ^ k + C * x * x ^ k := by linarith
  have f1 : (1 + ε) * y * a ^ k ≤ (1 + ε) * y * (z + x' + y) ^ k :=
    mul_le_mul_of_nonneg_left hA (mul_nonneg (by linarith) hy)
  have f2 : C * x * x ^ k ≤ C * x * (z + x + y') ^ k :=
    mul_le_mul_of_nonneg_left hB (mul_nonneg hC0 hx)
  linarith

end Aux_WCBR_l14

open WeightedCongestionBR Aux_WCBR_l14 in
theorem solution (d : ℕ) (hd : 1 ≤ d) (f : Polynomial ℝ) (hf : IsPd d f) (ε : ℝ) (hε : 0 < ε)
    (x x' y y' z : ℝ) (hx : 0 ≤ x) (hx' : 0 ≤ x') (hy : 0 ≤ y) (hy' : 0 ≤ y') (hz : 0 ≤ z) :
    y * f.eval (z + x + y) ≤
      (1 + ε) * y * f.eval (z + x' + y) + (1 + 1 / ε) ^ d * (d : ℝ) ^ d * x * f.eval (z + x + y') := by
  have hlt : f.natDegree < d + 1 := Nat.lt_succ_of_le hf.1
  simp only [Polynomial.eval_eq_sum_range' hlt]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k hk
  have hkd : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hm := mono d hd k hkd ε hε x x' y y' z hx hx' hy hy' hz
  have hc := hf.2 k
  have := mul_le_mul_of_nonneg_left hm hc
  calc y * (f.coeff k * (z + x + y) ^ k) = f.coeff k * (y * (z + x + y) ^ k) := by ring
    _ ≤ f.coeff k * ((1 + ε) * y * (z + x' + y) ^ k +
          (1 + 1 / ε) ^ d * (d : ℝ) ^ d * x * (z + x + y') ^ k) := this
    _ = (1 + ε) * y * (f.coeff k * (z + x' + y) ^ k) +
          (1 + 1 / ε) ^ d * (d : ℝ) ^ d * x * (f.coeff k * (z + x + y') ^ k) := by ring
