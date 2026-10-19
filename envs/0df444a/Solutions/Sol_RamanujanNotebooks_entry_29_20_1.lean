-- Prove2me | solution 1 for RamanujanNotebooks.entry_29_20_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T18:12:59.055087+00:00
-- url     : https://prove2.me/submissions/3d0e363d-71b1-47a9-bf42-3b004f303ab6

import Mathlib
import Definitions.Def_RamanujanNotebooks_shared_shiftedFactorialR

open Filter Topology RamanujanNotebooks

namespace RN29

noncomputable abbrev P (n : ℕ) : ℝ := shiftedFactorialR (1 / 2) n

lemma P_succ (n : ℕ) : P (n + 1) = P n * (1 / 2 + n) := by
  simp [P, shiftedFactorialR, Finset.prod_range_succ]

lemma P_pos (n : ℕ) : 0 < P n := by
  unfold P shiftedFactorialR
  exact Finset.prod_pos fun j _ => by positivity

lemma P_le (n : ℕ) : P n ≤ n.factorial := by
  induction n with
  | zero => simp [P, shiftedFactorialR]
  | succ n ih =>
    rw [P_succ, Nat.factorial_succ]
    push_cast
    calc P n * (1 / 2 + n) ≤ n.factorial * ((n : ℝ) + 1) :=
          mul_le_mul ih (by linarith) (by positivity) (by positivity)
      _ = _ := by ring

noncomputable def B (n k : ℕ) : ℝ :=
  P n ^ 3 * P k ^ 2 / ((n.factorial : ℝ) * ((n + k).factorial : ℝ) ^ 2 * 4 ^ n)

noncomputable def F (n k : ℕ) : ℝ := (6 * n + 4 * k + 1) * B n k

noncomputable def G (n k : ℕ) : ℝ := 8 * n * B n k

lemma B_pos (n k : ℕ) : 0 < B n k := by
  unfold B; have := P_pos n; have := P_pos k; positivity

lemma B_succ_left (n k : ℕ) :
    B (n + 1) k = B n k * ((1 / 2 + n) ^ 3 / ((n + 1) * (n + k + 1) ^ 2 * 4)) := by
  unfold B
  rw [P_succ, show n + 1 + k = (n + k) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring

lemma B_succ_right (n k : ℕ) :
    B n (k + 1) = B n k * ((1 / 2 + k) ^ 2 / (n + k + 1) ^ 2) := by
  unfold B
  rw [P_succ, show n + (k + 1) = (n + k) + 1 by omega, Nat.factorial_succ]
  push_cast
  field_simp

lemma wz (n k : ℕ) : F n (k + 1) - F n k = G (n + 1) k - G n k := by
  unfold F G
  rw [B_succ_right, B_succ_left]
  push_cast
  field_simp
  ring

lemma B_le (n k : ℕ) : B n k ≤ (1 / 4) ^ n := by
  unfold B
  have h1 := P_le n
  have h2 := P_le k
  have h3 : (n.factorial : ℝ) * k.factorial ≤ (n + k).factorial := by
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add n k)
  have hP := P_pos n; have hQ := P_pos k
  have hn : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  rw [div_le_iff₀ (by positivity), one_div, inv_pow, inv_mul_eq_div, le_div_iff₀ (by positivity)]
  calc P n ^ 3 * P k ^ 2 * 4 ^ n ≤ (n.factorial : ℝ) ^ 3 * (k.factorial : ℝ) ^ 2 * 4 ^ n := by gcongr
    _ = n.factorial * ((n.factorial : ℝ) * k.factorial) ^ 2 * 4 ^ n := by ring
    _ ≤ n.factorial * ((n + k).factorial : ℝ) ^ 2 * 4 ^ n := by gcongr

lemma B_le' (n k : ℕ) : B (n + 1) k ≤ (1 / 4) ^ (n + 1) / ((k : ℝ) + 1) ^ 2 := by
  unfold B
  have h1 := P_le (n + 1)
  have h2 := P_le k
  have h3 : ((n + 1).factorial : ℝ) * k.factorial * (k + 1) ≤ (n + 1 + k).factorial := by
    have e := Nat.add_choose_mul_factorial_mul_factorial (n + 1) k
    have c : k + 1 ≤ (n + 1 + k).choose k := by
      calc k + 1 = (k + 1).choose k := by simp [Nat.choose_succ_self_right]
        _ ≤ (n + 1 + k).choose k := Nat.choose_le_choose k (by omega)
    have : ((n + 1).factorial) * k.factorial * (k + 1) ≤ (n + 1 + k).factorial := by
      rw [← e]
      calc (n + 1).factorial * k.factorial * (k + 1) = (k + 1) * (n + 1).factorial * k.factorial := by ring
        _ ≤ _ := by gcongr
    exact_mod_cast this
  have hP := P_pos (n + 1); have hQ := P_pos k
  have hn : (0 : ℝ) < (n + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have key : P (n + 1) ^ 3 * P k ^ 2 * ((k : ℝ) + 1) ^ 2
      ≤ (n + 1).factorial * ((n + 1 + k).factorial : ℝ) ^ 2 := by
    calc P (n + 1) ^ 3 * P k ^ 2 * ((k : ℝ) + 1) ^ 2
        ≤ ((n + 1).factorial : ℝ) ^ 3 * (k.factorial : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 2 := by gcongr
      _ = (n + 1).factorial * (((n + 1).factorial : ℝ) * k.factorial * (k + 1)) ^ 2 := by ring
      _ ≤ (n + 1).factorial * ((n + 1 + k).factorial : ℝ) ^ 2 := by gcongr
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  refine key.trans (le_of_eq ?_)
  rw [one_div, inv_pow]
  field_simp


lemma F_nonneg (n k : ℕ) : 0 ≤ F n k := by unfold F; have := B_pos n k; positivity

lemma F_le (n k : ℕ) : F n k ≤ (6 * n + 4 * k + 1) * (1 / 4) ^ n := by
  unfold F; gcongr; exact B_le n k

lemma summable_geom_lin (a b : ℝ) : Summable fun n : ℕ => (a * n + b) * (1 / 4 : ℝ) ^ n := by
  have h1 : Summable fun n : ℕ => (n : ℝ) ^ 1 * (1 / 4 : ℝ) ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num)
  have h2 : Summable fun n : ℕ => (1 / 4 : ℝ) ^ n := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine ((h1.mul_left a).add (h2.mul_left b)).congr fun n => ?_
  simp only [pow_one]; ring

lemma F_summable (k : ℕ) : Summable fun n => F n k := by
  refine Summable.of_nonneg_of_le (fun n => F_nonneg n k) (fun n => F_le n k) ?_
  convert summable_geom_lin 6 (4 * k + 1) using 1
  funext n; ring

noncomputable def S (k : ℕ) : ℝ := ∑' n, F n k

lemma G_tendsto (k : ℕ) : Tendsto (fun N => G N k) atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => 8 * ((N : ℝ) * (1 / 4 : ℝ) ^ N)) atTop (𝓝 (8 * 0)) :=
    (tendsto_self_mul_const_pow_of_lt_one (by norm_num) (by norm_num)).const_mul 8
  rw [mul_zero] at h
  refine squeeze_zero (fun N => ?_) (fun N => ?_) h
  · unfold G; have := B_pos N k; positivity
  · unfold G; rw [mul_assoc]; gcongr; exact B_le N k

lemma S_succ (k : ℕ) : S (k + 1) = S k := by
  have hs := ((F_summable (k + 1)).hasSum.sub (F_summable k).hasSum)
  have ht := hs.tendsto_sum_nat
  have hp : ∀ N, ∑ i ∈ Finset.range N, (F i (k + 1) - F i k) = G N k := by
    intro N
    rw [Finset.sum_congr rfl (fun i _ => wz i k), Finset.sum_range_sub (fun n => G n k)]
    simp [G]
  simp_rw [hp] at ht
  have := tendsto_nhds_unique ht (G_tendsto k)
  unfold S; linarith

lemma S_eq (k : ℕ) : S k = S 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [S_succ, ih]

noncomputable def C0 : ℝ := ∑' n : ℕ, (6 * n + 11) * (1 / 4 : ℝ) ^ n

lemma tail_le (k : ℕ) : ∑' n, F (n + 1) k ≤ C0 / ((k : ℝ) + 1) := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hb : ∀ n : ℕ, F (n + 1) k ≤ (6 * n + 11) * (1 / 4 : ℝ) ^ n / ((k : ℝ) + 1) := by
    intro n
    unfold F
    calc (6 * ((n + 1 : ℕ) : ℝ) + 4 * k + 1) * B (n + 1) k
        ≤ (6 * ((n + 1 : ℕ) : ℝ) + 4 * k + 1) * ((1 / 4) ^ (n + 1) / ((k : ℝ) + 1) ^ 2) := by
          gcongr; exact B_le' n k
      _ ≤ ((6 * n + 11) * ((k : ℝ) + 1)) * ((1 / 4) ^ n / ((k : ℝ) + 1) ^ 2) := by
          refine mul_le_mul ?_ (div_le_div_of_nonneg_right
            (pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1 / 4) (by norm_num) (Nat.le_succ n))
            (by positivity)) (by positivity) (by positivity)
          push_cast; nlinarith
      _ = _ := by field_simp
  have hsum : Summable fun n : ℕ => (6 * n + 11) * (1 / 4 : ℝ) ^ n / ((k : ℝ) + 1) :=
    (summable_geom_lin 6 11).div_const _
  calc ∑' n, F (n + 1) k ≤ ∑' n : ℕ, (6 * n + 11) * (1 / 4 : ℝ) ^ n / ((k : ℝ) + 1) :=
        Summable.tsum_le_tsum hb ((summable_nat_add_iff 1).mpr (F_summable k)) hsum
    _ = C0 / ((k : ℝ) + 1) := by rw [C0, tsum_div_const]

lemma wallis_rel (k : ℕ) : (P k / k.factorial) ^ 2 * (2 * k + 1) * Real.Wallis.W k = 1 := by
  induction k with
  | zero => simp [P, shiftedFactorialR, Real.Wallis.W]
  | succ k ih =>
    rw [Real.Wallis.W_succ, P_succ, Nat.factorial_succ]
    have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    calc _ = (P k / k.factorial) ^ 2 * (2 * k + 1) * Real.Wallis.W k := by
          push_cast; field_simp; ring
      _ = 1 := ih

lemma F0_tendsto : Tendsto (fun k => F 0 k) atTop (𝓝 (4 / Real.pi)) := by
  have hF : ∀ k : ℕ, F 0 k = (4 * k + 1) / (2 * k + 1) / Real.Wallis.W k := by
    intro k
    have hw := wallis_rel k
    have hW := Real.Wallis.W_pos k
    have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    unfold F B
    simp only [Nat.cast_zero, mul_zero, zero_add, Nat.factorial_zero, Nat.cast_one, pow_zero]
    have hP0 : P 0 = 1 := by simp [P, shiftedFactorialR]
    rw [hP0]
    field_simp
    field_simp at hw
    linear_combination hw
  simp_rw [hF]
  have h1 : Tendsto (fun k : ℕ => (4 * (k : ℝ) + 1) / (2 * k + 1)) atTop (𝓝 2) := by
    have : Tendsto (fun k : ℕ => (2 : ℝ) - 1 / (2 * k + 1)) atTop (𝓝 (2 - 0)) := by
      refine tendsto_const_nhds.sub ?_
      refine tendsto_const_nhds.div_atTop ?_
      exact tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos)
    rw [sub_zero] at this
    refine this.congr fun k => ?_
    field_simp; ring
  have h2 := h1.div Real.Wallis.tendsto_W_nhds_pi_div_two (by positivity)
  have e : (4 : ℝ) / Real.pi = 2 / (Real.pi / 2) := by field_simp; ring
  rw [e]; exact h2

lemma S0 : S 0 = 4 / Real.pi := by
  have hsplit : ∀ k, S 0 = F 0 k + ∑' n, F (n + 1) k := by
    intro k; rw [← S_eq k, S, (F_summable k).tsum_eq_zero_add]
  have htail : Tendsto (fun k : ℕ => ∑' n, F (n + 1) k) atTop (𝓝 0) := by
    have : Tendsto (fun k : ℕ => C0 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    exact squeeze_zero (fun k => tsum_nonneg fun n => F_nonneg _ _) tail_le this
  have h := F0_tendsto.add htail
  rw [add_zero] at h
  have hc : Tendsto (fun k : ℕ => F 0 k + ∑' n, F (n + 1) k) atTop (𝓝 (S 0)) := by
    simp_rw [← hsplit]; exact tendsto_const_nhds
  exact tendsto_nhds_unique hc h

end RN29

theorem solution :
    HasSum
      (fun n : ℕ =>
        (6 * (n : ℝ) + 1) * shiftedFactorialR (1 / 2) n ^ 3
          / (4 ^ n * (n.factorial : ℝ) ^ 3))
      (4 / Real.pi) := by
  have h := (RN29.F_summable 0).hasSum
  rw [show (∑' n, RN29.F n 0) = 4 / Real.pi from RN29.S0] at h
  convert h using 1
  funext n
  simp only [RN29.F, RN29.B, RN29.P, Nat.cast_zero, mul_zero, add_zero]
  simp [shiftedFactorialR]
  ring
