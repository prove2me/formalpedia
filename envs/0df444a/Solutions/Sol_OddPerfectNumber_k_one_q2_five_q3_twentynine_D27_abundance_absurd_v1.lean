-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_D27_abundance_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T05:11:56.991513+00:00
-- url     : https://prove2.me/submissions/c0c9c697-1864-4f0d-918c-ff8951f87cf1

import Mathlib

set_option autoImplicit false

namespace B8cc565cAux

lemma geom_cast (x n : ℕ) :
    (∑ i ∈ Finset.range n, (x : ℝ) ^ i) * ((x : ℝ) - 1) = (x : ℝ) ^ n - 1 :=
  geom_sum_mul (x : ℝ) n

lemma real_core (A B C E X Y Z W q : ℝ)
    (hX : (3:ℝ) ^ 16 ≤ X) (hY : (5:ℝ) ^ 12 ≤ Y) (hZ : (29:ℝ) ^ 8 ≤ Z) (hW : (30:ℝ) ^ 4 ≤ W)
    (hA : A * 2 = 3 * X - 1) (hB : B * 4 = 5 * Y - 1) (hC : C * 28 = 29 * Z - 1)
    (hE : E * (q - 1) = q * W - 1) (hq : 30 ≤ q)
    (key : 27 * (A * B * C * E) = 53 * (X * Y * Z * W))
    (hcase : q ≤ 89 ∨ 94 ≤ q) : False := by
  have hXp : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hYp : 0 < Y := lt_of_lt_of_le (by norm_num) hY
  have hZp : 0 < Z := lt_of_lt_of_le (by norm_num) hZ
  have hWp : 0 < W := lt_of_lt_of_le (by norm_num) hW
  have hAp : 0 < A := by nlinarith
  have hBp : 0 < B := by nlinarith
  have hCp : 0 < C := by nlinarith
  have hq1 : 0 < q - 1 := by linarith
  have hEp : 0 < E := by
    by_contra h0
    have h := not_lt.mp h0
    have : E * (q - 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hq1.le
    nlinarith
  have hXYZ : 0 < X * Y * Z := by positivity
  rcases hcase with hle | hge
  · -- lower bounds
    have hA' : 14999 / 10000 * X ≤ A := by nlinarith
    have hB' : 12499 / 10000 * Y ≤ B := by nlinarith
    have hC' : 10357 / 10000 * Z ≤ C := by nlinarith
    have hE' : 10113 / 10000 * W ≤ E := by
      have h1 : 10113 / 10000 * W * (q - 1) ≤ E * (q - 1) := by
        rw [hE]; nlinarith [mul_nonneg (sub_nonneg.mpr hle) hWp.le]
      exact le_of_mul_le_mul_right h1 hq1
    have hAB : 14999 / 10000 * X * (12499 / 10000 * Y) ≤ A * B :=
      mul_le_mul hA' hB' (by positivity) hAp.le
    have hABC : 14999 / 10000 * X * (12499 / 10000 * Y) * (10357 / 10000 * Z) ≤ A * B * C :=
      mul_le_mul hAB hC' (by positivity) (by positivity)
    have hABCE : 14999 / 10000 * X * (12499 / 10000 * Y) * (10357 / 10000 * Z)
        * (10113 / 10000 * W) ≤ A * B * C * E :=
      mul_le_mul hABC hE' (by positivity) (by positivity)
    have hXYZW : 0 < X * Y * Z * W := by positivity
    nlinarith
  · -- upper bounds
    have hA' : A < 3 / 2 * X := by linarith
    have hB' : B < 5 / 4 * Y := by linarith
    have hC' : C < 29 / 28 * Z := by linarith
    have hAB : A * B < 3 / 2 * X * (5 / 4 * Y) :=
      mul_lt_mul'' hA' hB' hAp.le hBp.le
    have hABC : A * B * C < 3 / 2 * X * (5 / 4 * Y) * (29 / 28 * Z) :=
      mul_lt_mul'' hAB hC' (by positivity) hCp.le
    have h1 : A * B * C * E < 3 / 2 * X * (5 / 4 * Y) * (29 / 28 * Z) * E :=
      mul_lt_mul_of_pos_right hABC hEp
    -- 53 * XYZ * W < 27 * (435/224) * XYZ * E
    have h2 : (X * Y * Z) * (53 * W) < (X * Y * Z) * (27 * (435 / 224) * E) := by
      nlinarith
    have h3 : 53 * W < 27 * (435 / 224) * E := lt_of_mul_lt_mul_left h2 hXYZ.le
    have h4 : 53 * W * (q - 1) < 27 * (435 / 224) * E * (q - 1) :=
      mul_lt_mul_of_pos_right h3 hq1
    have h5 : 53 * W * (q - 1) < 27 * (435 / 224) * (q * W) := by
      have : 27 * (435 / 224) * E * (q - 1) = 27 * (435 / 224) * (q * W - 1) := by
        rw [mul_assoc (27 * (435 / 224)) E, hE]
      nlinarith
    have h6 : W * (11872 - 127 * q) < 0 := by nlinarith
    have h7 : 0 ≤ W * (127 * q - 11872) := mul_nonneg hWp.le (by linarith)
    nlinarith

end B8cc565cAux

theorem solution (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hD : D = 27) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 29 < q4) (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e) : False := by
  subst hD
  subst hp_eq
  rw [hsigma, hfac] at hrel
  have hrelR := congrArg (Nat.cast : ℕ → ℝ) hrel
  push_cast at hrelR
  have hcase : q4 ≤ 89 ∨ 94 ≤ q4 := by
    rcases (show q4 ≤ 89 ∨ 94 ≤ q4 ∨ (90 ≤ q4 ∧ q4 ≤ 93) by omega) with h | h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      interval_cases q4 <;> norm_num at hq4prime
  have hcaseR : (q4 : ℝ) ≤ 89 ∨ 94 ≤ (q4 : ℝ) := by
    rcases hcase with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  have hq : (30 : ℝ) ≤ q4 := by exact_mod_cast hq4gt
  have g3 := B8cc565cAux.geom_cast 3 (2*a+1)
  have g5 := B8cc565cAux.geom_cast 5 (2*b+1)
  have g29 := B8cc565cAux.geom_cast 29 (2*c+1)
  have gq := B8cc565cAux.geom_cast q4 (2*e+1)
  push_cast at g3 g5 g29 gq
  have hX : (3:ℝ) ^ 16 ≤ (3:ℝ) ^ (2*a) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hY : (5:ℝ) ^ 12 ≤ (5:ℝ) ^ (2*b) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hZ : (29:ℝ) ^ 8 ≤ (29:ℝ) ^ (2*c) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hW : (30:ℝ) ^ 4 ≤ (q4:ℝ) ^ (2*e) := by
    calc (30:ℝ) ^ 4 ≤ (q4:ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hq 4
      _ ≤ (q4:ℝ) ^ (2*e) := pow_le_pow_right₀ (by linarith) (by omega)
  rw [pow_succ] at g3 g5 g29 gq
  refine B8cc565cAux.real_core (∑ i ∈ Finset.range (2*a+1), (3:ℝ)^i) (∑ i ∈ Finset.range (2*b+1), (5:ℝ)^i)
    (∑ i ∈ Finset.range (2*c+1), (29:ℝ)^i) (∑ i ∈ Finset.range (2*e+1), (q4:ℝ)^i)
    ((3:ℝ)^(2*a)) ((5:ℝ)^(2*b)) ((29:ℝ)^(2*c)) ((q4:ℝ)^(2*e)) (q4 : ℝ) hX hY hZ hW ?_ ?_ ?_ ?_ hq ?_ hcaseR
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
