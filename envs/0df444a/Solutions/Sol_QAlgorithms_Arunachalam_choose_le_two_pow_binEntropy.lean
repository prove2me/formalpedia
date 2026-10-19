-- Prove2me | solution 1 for QAlgorithms.Arunachalam.choose_le_two_pow_binEntropy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T07:47:38.670596+00:00
-- url     : https://prove2.me/submissions/e9b31c10-1cd9-48a5-831c-af2f60888aab

import Definitions.Def_QAlgorithms_Defs_Information

open Finset QAlgorithms

private lemma entropy_weight {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (hkn : k < n) :
    (((k : ℝ) / n) ^ k * (1 - (k : ℝ) / n) ^ (n - k))⁻¹ =
      (2 : ℝ) ^ ((n : ℝ) * binEntropy2 ((k : ℝ) / n)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : (0 : ℝ) < (k : ℝ) / n := div_pos (by exact_mod_cast hk) hn'
  have hq : (0 : ℝ) < 1 - (k : ℝ) / n := by
    have : (k : ℝ) / n < 1 := (div_lt_one hn').2 (by exact_mod_cast hkn)
    linarith
  apply Real.log_injOn_pos (inv_pos.mpr (mul_pos (pow_pos hp _) (pow_pos hq _)))
    (Real.rpow_pos_of_pos (by norm_num) _)
  rw [Real.log_inv, Real.log_mul (ne_of_gt (pow_pos hp _))
    (ne_of_gt (pow_pos hq _)), Real.log_pow, Real.log_pow, Real.log_rpow (by norm_num)]
  unfold binEntropy2 Real.binEntropy
  rw [Real.log_inv, Real.log_inv, Nat.cast_sub hkn.le]
  have hl : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  ring

private lemma binomial_mass (n : ℕ) (p : ℝ) :
    ∑ i ∈ range (n + 1), (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i)) = 1 := by
  have h := add_pow p (1 - p) n
  rw [show p + (1 - p) = 1 by ring, one_pow] at h
  calc
    _ = ∑ i ∈ range (n + 1), p ^ i * (1 - p) ^ (n - i) * (n.choose i : ℝ) := by
      apply sum_congr rfl
      intro i hi
      ring
    _ = 1 := h.symm

private lemma weight_decreasing {n m i : ℕ} {p : ℝ} (hp : 0 ≤ p)
    (hpq : p ≤ 1 - p) (him : i ≤ m) (hmn : m ≤ n) :
    p ^ m * (1 - p) ^ (n - m) ≤ p ^ i * (1 - p) ^ (n - i) := by
  have hq : 0 ≤ 1 - p := hp.trans hpq
  have hm : i + (m - i) = m := by omega
  have hn : (n - m) + (m - i) = n - i := by omega
  calc
    p ^ m * (1 - p) ^ (n - m) =
        (p ^ i * (1 - p) ^ (n - m)) * p ^ (m - i) := by
          nth_rw 1 [← hm]
          rw [pow_add]; ring
    _ ≤ (p ^ i * (1 - p) ^ (n - m)) * (1 - p) ^ (m - i) := by
      gcongr
    _ = p ^ i * (1 - p) ^ (n - i) := by rw [← hn, pow_add]; ring

theorem solution {n : ℕ} (hn : 1 ≤ n) :
    (∀ k : ℕ, k ≤ n →
        ((n.choose k : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * binEntropy2 ((k : ℝ) / (n : ℝ)))) ∧
      ∀ m : ℕ, 2 * m ≤ n →
        ∑ i ∈ Finset.range (m + 1), ((n.choose i : ℕ) : ℝ) ≤
          (2 : ℝ) ^ ((n : ℝ) * binEntropy2 ((m : ℝ) / (n : ℝ))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · intro k hkn
    by_cases hk : k = 0
    · subst k; simp [binEntropy2]
    by_cases hke : k = n
    · subst k; simp [binEntropy2, ne_of_gt hn']
    have hk0 : 0 < k := Nat.pos_of_ne_zero hk
    have hkn' : k < n := lt_of_le_of_ne hkn hke
    rw [← entropy_weight (by omega) hk0 hkn']
    have hp : (0 : ℝ) < (k : ℝ) / n := div_pos (by exact_mod_cast hk0) hn'
    have hq : (0 : ℝ) < 1 - (k : ℝ) / n := by
      have : (k : ℝ) / n < 1 := (div_lt_one hn').2 (by exact_mod_cast hkn')
      linarith
    rw [← one_div]
    apply (le_div_iff₀ (by positivity)).2
    calc
      _ ≤ ∑ i ∈ range (n + 1), (n.choose i : ℝ) *
          (((k : ℝ) / n) ^ i * (1 - (k : ℝ) / n) ^ (n - i)) := by
        exact single_le_sum (f := fun i : ℕ => (n.choose i : ℝ) *
          (((k : ℝ) / n) ^ i * (1 - (k : ℝ) / n) ^ (n - i)))
          (fun i hi => by positivity) (mem_range.mpr (by omega))
      _ = 1 := binomial_mass n _
  · intro m hmn
    by_cases hm : m = 0
    · subst m; simp [binEntropy2]
    have hm0 : 0 < m := Nat.pos_of_ne_zero hm
    have hmn' : m < n := by omega
    rw [← entropy_weight (by omega) hm0 hmn']
    have hp : (0 : ℝ) < (m : ℝ) / n := div_pos (by exact_mod_cast hm0) hn'
    have hpq : (m : ℝ) / n ≤ 1 - (m : ℝ) / n := by
      have h : (2 : ℝ) * m ≤ n := by exact_mod_cast hmn
      have : (m : ℝ) / n ≤ 1 / 2 := (div_le_iff₀ hn').2 (by linarith)
      linarith
    have hq : (0 : ℝ) < 1 - (m : ℝ) / n := hp.trans_le hpq
    rw [← one_div]
    apply (le_div_iff₀ (by positivity)).2
    rw [sum_mul]
    calc
      _ ≤ ∑ i ∈ range (m + 1), (n.choose i : ℝ) *
          (((m : ℝ) / n) ^ i * (1 - (m : ℝ) / n) ^ (n - i)) := by
        apply sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact weight_decreasing hp.le hpq (by simpa using hi) hmn'.le
      _ ≤ ∑ i ∈ range (n + 1), (n.choose i : ℝ) *
          (((m : ℝ) / n) ^ i * (1 - (m : ℝ) / n) ^ (n - i)) := by
        apply sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
        intros; positivity
      _ = 1 := binomial_mass n _
