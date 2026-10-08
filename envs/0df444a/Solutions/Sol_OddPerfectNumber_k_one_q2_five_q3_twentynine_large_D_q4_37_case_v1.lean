-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_37_case_v1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T19:17:17.798995+00:00
-- url     : https://prove2.me/submissions/30b562bc-2c92-4885-af4f-b240b826dbcf

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_37_D_le_244_v1

set_option autoImplicit false

namespace Aux365efcc2

lemma geom_cast (x n : ℕ) :
    (∑ i ∈ Finset.range n, (x : ℝ) ^ i) * ((x : ℝ) - 1) = (x : ℝ) ^ n - 1 :=
  geom_sum_mul (x : ℝ) n

lemma upper_core (A B C E X Y Z W Dr : ℝ)
    (hX : (3:ℝ) ^ 16 ≤ X) (hY : (5:ℝ) ^ 12 ≤ Y) (hZ : (29:ℝ) ^ 8 ≤ Z) (hW : (37:ℝ) ^ 4 ≤ W)
    (hA : A * 2 = 3 * X - 1) (hB : B * 4 = 5 * Y - 1) (hC : C * 28 = 29 * Z - 1)
    (hE : E * 36 = 37 * W - 1) (hD : 1 ≤ Dr)
    (key : Dr * (A * B * C * E) = (2 * Dr - 1) * (X * Y * Z * W)) : 33 * Dr < 8064 := by
  have hXp : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hYp : 0 < Y := lt_of_lt_of_le (by norm_num) hY
  have hZp : 0 < Z := lt_of_lt_of_le (by norm_num) hZ
  have hWp : 0 < W := lt_of_lt_of_le (by norm_num) hW
  have hAp : 0 < A := by nlinarith
  have hBp : 0 < B := by nlinarith
  have hCp : 0 < C := by nlinarith
  have hEp : 0 < E := by nlinarith
  have hA' : A < 3 / 2 * X := by linarith
  have hB' : B < 5 / 4 * Y := by linarith
  have hC' : C < 29 / 28 * Z := by linarith
  have hE' : E < 37 / 36 * W := by linarith
  have hAB : A * B < 3 / 2 * X * (5 / 4 * Y) := mul_lt_mul'' hA' hB' hAp.le hBp.le
  have hABC : A * B * C < 3 / 2 * X * (5 / 4 * Y) * (29 / 28 * Z) :=
    mul_lt_mul'' hAB hC' (by positivity) hCp.le
  have hABCE : A * B * C * E < 3 / 2 * X * (5 / 4 * Y) * (29 / 28 * Z) * (37 / 36 * W) :=
    mul_lt_mul'' hABC hE' (by positivity) hEp.le
  have hP : 0 < X * Y * Z * W := by positivity
  have h1 : Dr * (A * B * C * E) < Dr * (16095 / 8064 * (X * Y * Z * W)) := by
    apply mul_lt_mul_of_pos_left _ (by linarith)
    calc A * B * C * E < 3 / 2 * X * (5 / 4 * Y) * (29 / 28 * Z) * (37 / 36 * W) := hABCE
      _ = 16095 / 8064 * (X * Y * Z * W) := by ring
  rw [key] at h1
  have h2 : (2 * Dr - 1) * (X * Y * Z * W) < (16095 / 8064 * Dr) * (X * Y * Z * W) := by
    calc (2 * Dr - 1) * (X * Y * Z * W) < Dr * (16095 / 8064 * (X * Y * Z * W)) := h1
      _ = (16095 / 8064 * Dr) * (X * Y * Z * W) := by ring
  have h3 := lt_of_mul_lt_mul_right h2 hP.le
  linarith

lemma lower_core (A B C E X Y Z W Dr : ℝ)
    (hX : (3:ℝ) ^ 16 ≤ X) (hY : (5:ℝ) ^ 12 ≤ Y) (hZ : (29:ℝ) ^ 8 ≤ Z) (hW : (37:ℝ) ^ 4 ≤ W)
    (hA : A * 2 = 3 * X - 1) (hB : B * 4 = 5 * Y - 1) (hC : C * 28 = 29 * Z - 1)
    (hE : E * 36 = 37 * W - 1) (hD : 1 ≤ Dr) (hDle : Dr ≤ 244)
    (key : Dr * (A * B * C * E) = (2 * Dr - 1) * (X * Y * Z * W)) : False := by
  have hXp : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hYp : 0 < Y := lt_of_lt_of_le (by norm_num) hY
  have hZp : 0 < Z := lt_of_lt_of_le (by norm_num) hZ
  have hWp : 0 < W := lt_of_lt_of_le (by norm_num) hW
  have hA' : 3 / 2 * (1 - 1 / 10000000) * X ≤ A := by nlinarith
  have hB' : 5 / 4 * (1 - 1 / 10000000) * Y ≤ B := by nlinarith
  have hC' : 29 / 28 * (1 - 1 / 10000000) * Z ≤ C := by nlinarith
  have hE' : 37 / 36 * (1 - 1 / 10000000) * W ≤ E := by nlinarith
  have hAB : 3 / 2 * (1 - 1 / 10000000) * X * (5 / 4 * (1 - 1 / 10000000) * Y) ≤ A * B :=
    mul_le_mul hA' hB' (by positivity) (le_trans (by positivity) hA')
  have hABC : 3 / 2 * (1 - 1 / 10000000) * X * (5 / 4 * (1 - 1 / 10000000) * Y)
      * (29 / 28 * (1 - 1 / 10000000) * Z) ≤ A * B * C :=
    mul_le_mul hAB hC' (by positivity) (le_trans (by positivity) hAB)
  have hABCE : 3 / 2 * (1 - 1 / 10000000) * X * (5 / 4 * (1 - 1 / 10000000) * Y)
      * (29 / 28 * (1 - 1 / 10000000) * Z) * (37 / 36 * (1 - 1 / 10000000) * W)
      ≤ A * B * C * E :=
    mul_le_mul hABC hE' (by positivity) (le_trans (by positivity) hABC)
  have hP : 0 < X * Y * Z * W := by positivity
  set c : ℝ := 3 / 2 * (1 - 1 / 10000000) * (5 / 4 * (1 - 1 / 10000000))
      * (29 / 28 * (1 - 1 / 10000000)) * (37 / 36 * (1 - 1 / 10000000)) with hc
  have hc_val : (2 - 1 / 244 : ℝ) < c := by rw [hc]; norm_num
  have hlow : c * (X * Y * Z * W) ≤ A * B * C * E := by
    have : c * (X * Y * Z * W) = 3 / 2 * (1 - 1 / 10000000) * X * (5 / 4 * (1 - 1 / 10000000) * Y)
      * (29 / 28 * (1 - 1 / 10000000) * Z) * (37 / 36 * (1 - 1 / 10000000) * W) := by
      rw [hc]; ring
    rw [this]; exact hABCE
  have h1 : Dr * (c * (X * Y * Z * W)) ≤ Dr * (A * B * C * E) :=
    mul_le_mul_of_nonneg_left hlow (by linarith)
  rw [key] at h1
  have h2 : (Dr * c) * (X * Y * Z * W) ≤ (2 * Dr - 1) * (X * Y * Z * W) := by
    calc (Dr * c) * (X * Y * Z * W) = Dr * (c * (X * Y * Z * W)) := by ring
      _ ≤ (2 * Dr - 1) * (X * Y * Z * W) := h1
  have h3 := le_of_mul_le_mul_right h2 hP
  nlinarith [mul_lt_mul_of_pos_right hc_val (show (0:ℝ) < Dr by linarith)]

end Aux365efcc2

open Finset in
theorem solution (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDlow : 75 ≤ D) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4eq : q4 = 37) (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e) : D = 225 ∧ p = 449 := by
  exfalso
  subst hq4eq
  subst hp_eq
  rw [hsigma, hfac] at hrel
  have hrelR := congrArg (Nat.cast : ℕ → ℝ) hrel
  have hsub : ((2 * D - 1 : ℕ) : ℝ) = 2 * (D : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  simp only [Nat.cast_mul] at hrelR
  rw [hsub] at hrelR
  push_cast at hrelR
  have g3 := Aux365efcc2.geom_cast 3 (2*a+1)
  have g5 := Aux365efcc2.geom_cast 5 (2*b+1)
  have g29 := Aux365efcc2.geom_cast 29 (2*c+1)
  have gq := Aux365efcc2.geom_cast 37 (2*e+1)
  push_cast at g3 g5 g29 gq
  have hX : (3:ℝ) ^ 16 ≤ (3:ℝ) ^ (2*a) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hY : (5:ℝ) ^ 12 ≤ (5:ℝ) ^ (2*b) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hZ : (29:ℝ) ^ 8 ≤ (29:ℝ) ^ (2*c) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hW : (37:ℝ) ^ 4 ≤ (37:ℝ) ^ (2*e) := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [pow_succ] at g3 g5 g29 gq
  have hD1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast (show 1 ≤ D by omega)
  have key : (D:ℝ) * ((∑ i ∈ Finset.range (2*a+1), (3:ℝ)^i) * (∑ i ∈ Finset.range (2*b+1), (5:ℝ)^i)
      * (∑ i ∈ Finset.range (2*c+1), (29:ℝ)^i) * (∑ i ∈ Finset.range (2*e+1), (37:ℝ)^i))
      = (2 * (D:ℝ) - 1) * ((3:ℝ)^(2*a) * (5:ℝ)^(2*b) * (29:ℝ)^(2*c) * (37:ℝ)^(2*e)) := by
    linear_combination hrelR
  have hup := Aux365efcc2.upper_core _ _ _ _ _ _ _ _ _ hX hY hZ hW
    (by linarith) (by linarith) (by linarith) (by linarith) hD1 key
  have hDle : D ≤ 244 := by
    have : (33 * D : ℝ) < 8064 := hup
    have h' : 33 * D < 8064 := by exact_mod_cast this
    omega
  have hDleR : (D:ℝ) ≤ 244 := by exact_mod_cast hDle
  exact Aux365efcc2.lower_core _ _ _ _ _ _ _ _ _ hX hY hZ hW
    (by linarith) (by linarith) (by linarith) (by linarith) hD1 hDleR key
