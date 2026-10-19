-- Prove2me | solution 1 for QAlgorithms.Childs.clockPathMatrix_gap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T20:33:09.6928+00:00
-- url     : https://prove2.me/submissions/5997be0a-24fe-42e7-a41c-8e168928149d

import Theorems.Thm_QAlgorithms_Childs_clockPathMatrix_eigenvalue_localization
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Real QAlgorithms

private lemma cosine_gap (n : ℝ) (hn : 3 ≤ n) :
    5 / (8 * n ^ 2) ≤ cos (π / (n + 1)) - cos (5 * π / (4 * n)) := by
  have hn0 : 0 < n := by linarith
  let a := π / (n + 1)
  let b := 5 * π / (4 * n)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hab : a ≤ π / n := by
    dsimp [a]; exact div_le_div_of_nonneg_left pi_pos.le hn0 (by linarith)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hba : π / (4 * n) ≤ b - a := by
    have heq : π / (4 * n) = b - π / n := by dsimp [b]; ring
    rw [heq]; linarith
  have hsum : 5 * π / (4 * n) ≤ b + a := by dsimp [b] at *; linarith
  have hbmax : b ≤ π / 2 := by
    dsimp [b]; apply (div_le_iff₀ (by positivity : 0 < 4 * n)).2
    nlinarith [pi_pos]
  have hp : 0 ≤ (b + a) / 2 := by positivity
  have hm : 0 ≤ (b - a) / 2 := by linarith [div_pos pi_pos (by positivity : 0 < 4 * n)]
  have hpmax : (b + a) / 2 ≤ π / 2 := by
    have : a ≤ b := by linarith [div_pos pi_pos (by positivity : 0 < 4 * n)]
    linarith
  have hmmax : (b - a) / 2 ≤ π / 2 := by linarith
  have sp := mul_le_sin hp hpmax
  have sm := mul_le_sin hm hmmax
  have hprod := mul_le_mul sp sm (by positivity) (sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith : (b + a) / 2 ≤ π))
  have hmin := mul_le_mul hsum hba (by positivity : 0 ≤ π / (4 * n)) (by positivity : 0 ≤ b + a)
  have hid : cos a - cos b = 2 * sin ((b + a) / 2) * sin ((b - a) / 2) := by
    rw [cos_sub_cos, show (a + b) / 2 = (b + a) / 2 by ring,
      show (a - b) / 2 = -((b - a) / 2) by ring, sin_neg]
    ring
  change 5 / (8 * n ^ 2) ≤ cos a - cos b
  rw [hid]
  have hp' : (b + a) * (b - a) / π ^ 2 ≤
      sin ((b + a) / 2) * sin ((b - a) / 2) := by
    calc
      (b + a) * (b - a) / π ^ 2 =
          2 / π * ((b + a) / 2) * (2 / π * ((b - a) / 2)) := by ring
      _ ≤ _ := hprod
  calc
    5 / (8 * n ^ 2) = 2 * ((5 * π / (4 * n)) * (π / (4 * n)) / π ^ 2) := by
      field_simp; ring
    _ ≤ 2 * ((b + a) * (b - a) / π ^ 2) := by
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hmin (sq_nonneg π)) (by norm_num)
    _ ≤ 2 * (sin ((b + a) / 2) * sin ((b - a) / 2)) := by linarith
    _ = 2 * sin ((b + a) / 2) * sin ((b - a) / 2) := by ring

private lemma pole_gap (n : ℝ) (hn : 1 ≤ n) :
    2 / n ^ 2 ≤ 1 - cos (π / n) := by
  have hn0 : 0 < n := by linarith
  have hb := cos_le_one_sub_mul_cos_sq (x := π / n) (by
    rw [abs_of_nonneg (by positivity : 0 ≤ π / n)]
    exact div_le_self pi_pos.le hn)
  have hpi := pi_pos
  field_simp at hb ⊢
  nlinarith

private lemma secular_test (n : ℝ) (hn : 32 ≤ n) :
    1 + 1 / n < sin ((n + 1) * (5 * π / (4 * n))) /
      sin (n * (5 * π / (4 * n))) := by
  have hn0 : 0 < n := by linarith
  let θ := 5 * π / (4 * n)
  have ht : 0 ≤ θ := by dsimp [θ]; positivity
  have htm : θ ≤ π / 2 := by
    dsimp [θ]; apply (div_le_iff₀ (by positivity : 0 < 4 * n)).2
    nlinarith [pi_pos]
  have hsin := mul_le_sin ht htm
  have hcos := one_sub_sq_div_two_le_cos (x := θ)
  have hsqrt : 0 < Real.sqrt 2 := by positivity
  have hnθ : n * θ = π / 4 + π := by dsimp [θ]; field_simp; ring
  have hplus : (n + 1) * θ = (π / 4 + π) + θ := by nlinarith [hnθ]
  have hid : sin ((n + 1) * θ) / sin (n * θ) = cos θ + sin θ := by
    rw [hplus, hnθ, sin_add, sin_add_pi, cos_add_pi, sin_pi_div_four, cos_pi_div_four]
    field_simp; ring
  change 1 + 1 / n < sin ((n + 1) * θ) / sin (n * θ)
  rw [hid]
  have hpi : π < 4 := pi_lt_four
  have hpisq : π ^ 2 < 16 := by nlinarith [pi_pos]
  dsimp [θ] at hsin hcos
  have hsin' : 5 / (2 * n) ≤ sin θ := by
    have heq : 5 / (2 * n) = 2 / π * (5 * π / (4 * n)) := by field_simp; norm_num
    rw [heq]
    exact hsin
  have hcos' : 1 - 25 * π ^ 2 / (32 * n ^ 2) ≤ cos θ := by
    have heq : 1 - 25 * π ^ 2 / (32 * n ^ 2) = 1 - (5 * π / (4 * n)) ^ 2 / 2 := by ring
    rw [heq]
    exact hcos
  have hbound : 25 * π ^ 2 / (32 * n ^ 2) < 3 / (2 * n) := by
    apply (div_lt_div_iff₀ (by positivity : 0 < 32 * n ^ 2) (by positivity : 0 < 2 * n)).2
    nlinarith [mul_pos hn0 (show 0 < 16 - π ^ 2 by linarith)]
  have hinv : 5 / (2 * n) - 1 / n = 3 / (2 * n) := by ring
  linarith

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ s ∈ Set.Icc (0 : ℝ) 1,
      c / (k : ℝ) ^ 2 ≤ spectralGap (clockPathMatrix k s) := by
  refine ⟨1 / 32, by norm_num, 32, ?_⟩
  intro k hk s hs
  have hk1 : 1 ≤ k := by omega
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hkn : (32 : ℝ) ≤ k := by exact_mod_cast hk
  have hn : (32 : ℝ) ≤ (k : ℝ) + 1 := by linarith
  obtain ⟨h0, h1, hcos, hlow, htest⟩ :=
    QAlgorithms.Childs.clockPathMatrix_eigenvalue_localization k hk1 s hs
  rw [spectralGap, dif_pos (by simp; omega)]
  have hbase : (1 / 32 : ℝ) / (k : ℝ) ^ 2 ≤ 1 / 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hk0)).2
    nlinarith [sq_nonneg ((k : ℝ) - 1)]
  by_cases hsmall : s ≤ 1 / 4
  · have : 1 / 4 ≤
        ascEigenvalues (clockPathMatrix k s) ⟨1, by simp; omega⟩ -
        ascEigenvalues (clockPathMatrix k s) ⟨0, by simp⟩ := by linarith
    exact hbase.trans this
  have hspos : 0 < s := by linarith
  have hn2 : ((k : ℝ) + 1) ^ 2 ≤ 4 * (k : ℝ) ^ 2 := by nlinarith
  by_cases hcrit : s ≤ ((k : ℝ) + 1) / (2 * (k : ℝ) + 3)
  · obtain ⟨hground, hexc⟩ := hlow hcrit
    have hgap := pole_gap ((k : ℝ) + 1) (by linarith)
    have hmul := mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ 2 * s)
    have hbound : (1 / 32 : ℝ) / (k : ℝ) ^ 2 ≤ 2 * s * (2 / ((k : ℝ) + 1) ^ 2) := by
      rw [show 2 * s * (2 / ((k : ℝ) + 1) ^ 2) = (4 * s) / ((k : ℝ) + 1) ^ 2 by ring]
      apply (div_le_div_iff₀ (sq_pos_of_pos hk0) (sq_pos_of_pos (by linarith : 0 < (k : ℝ) + 1))).2
      have hm := mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge hsmall)) (sq_nonneg (k : ℝ))
      nlinarith
    linarith
  · have hratio : (1 - s) / s < 1 + 1 / ((k : ℝ) + 1) := by
      apply (div_lt_iff₀ hspos).2
      have hc : ((k : ℝ) + 1) < s * (2 * (k : ℝ) + 3) :=
        (div_lt_iff₀ (by positivity)).1 (lt_of_not_ge hcrit)
      field_simp
      nlinarith
    have hθ : 5 * π / (4 * ((k : ℝ) + 1)) ∈
        Set.Ioo (π / ((k : ℝ) + 1)) (2 * π / ((k : ℝ) + 1)) := by
      constructor <;> (apply (div_lt_div_iff₀ (by positivity) (by positivity)).2; nlinarith [pi_pos])
    have htestval : 1 + 1 / ((k : ℝ) + 1) <
        sin (((k : ℝ) + 2) * (5 * π / (4 * ((k : ℝ) + 1)))) /
        sin (((k : ℝ) + 1) * (5 * π / (4 * ((k : ℝ) + 1)))) := by
      simpa only [add_assoc, show (1 : ℝ) + 1 = 2 by norm_num] using secular_test ((k : ℝ) + 1) hn
    have hexc := htest _ hθ hspos (hratio.trans htestval)
    have hgap : 5 / (8 * ((k : ℝ) + 1) ^ 2) ≤
        cos (π / ((k : ℝ) + 2)) - cos (5 * π / (4 * ((k : ℝ) + 1))) := by
      simpa only [add_assoc, show (1 : ℝ) + 1 = 2 by norm_num] using cosine_gap ((k : ℝ) + 1) (by linarith : (3 : ℝ) ≤ (k : ℝ) + 1)
    have hmul := mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ 2 * s)
    have hbound : (1 / 32 : ℝ) / (k : ℝ) ^ 2 ≤ 2 * s * (5 / (8 * ((k : ℝ) + 1) ^ 2)) := by
      rw [show 2 * s * (5 / (8 * ((k : ℝ) + 1) ^ 2)) = (5 * s / 4) / ((k : ℝ) + 1) ^ 2 by field_simp; ring]
      apply (div_le_div_iff₀ (sq_pos_of_pos hk0) (sq_pos_of_pos (by linarith : 0 < (k : ℝ) + 1))).2
      have hm := mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge hsmall)) (sq_nonneg (k : ℝ))
      nlinarith
    linarith
