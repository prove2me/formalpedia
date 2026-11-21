-- Prove2me | solution 1 for RandOnlineSetCoverSqrt.LowerBound.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:52:32.368942+00:00
-- url     : https://prove2.me/submissions/0904f048-8112-4788-b577-5d38b81252a2

import Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Candidates
import Theorems.Thm_RandOnlineSetCoverSqrt_LowerBound_lemma_3_3

section
namespace RandOnlineSetCoverSqrt.Dev.L35
open RandOnlineSetCoverSqrt.LowerBound

theorem choose_ratio (a N q : ℕ) (h : a ≤ N) :
    a.choose q * N ^ q ≤ a ^ q * N.choose q := by
  have desc : ∀ q, a.descFactorial q * N ^ q ≤ a ^ q * N.descFactorial q := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ, pow_succ]
      have h2 : (a - q) * N ≤ a * (N - q) := by
        rcases le_or_gt a q with hq | hq
        · simp [Nat.sub_eq_zero_of_le hq]
        · have : q ≤ N := by omega
          zify [hq.le, this]
          nlinarith
      calc (a - q) * a.descFactorial q * (N ^ q * N) = ((a - q) * N) * (a.descFactorial q * N ^ q) := by ring
        _ ≤ (a * (N - q)) * (a ^ q * N.descFactorial q) := Nat.mul_le_mul h2 ih
        _ = a ^ q * a * ((N - q) * N.descFactorial q) := by ring
  have := desc q
  rw [Nat.descFactorial_eq_factorial_mul_choose a q, Nat.descFactorial_eq_factorial_mul_choose N q] at this
  have hp := Nat.factorial_pos q
  nlinarith [this]

theorem choose_le_128 (m r : ℕ) (hr : 31 ≤ r) (h : m ≤ 33 * r) :
    (m.choose r : ℝ) ≤ 128 ^ r := by
  have hr0 : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hf : (0:ℝ) < (r.factorial : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos r)
  have h1 : (m.choose r : ℝ) ≤ (m:ℝ)^r / r.factorial := Nat.choose_le_pow_div r m
  have h2 : (r:ℝ)^r / r.factorial ≤ Real.exp r := Real.pow_div_factorial_le_exp (r:ℝ) hr0.le r
  rw [div_le_iff₀ hf] at h2
  have he : Real.exp (r:ℝ) = Real.exp 1 ^ r := by rw [← Real.exp_nat_mul]; simp
  have he3 : Real.exp 1 ^ r ≤ 3 ^ r := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le r
  have hm : (m:ℝ) ^ r ≤ (33:ℝ) ^ r * (r:ℝ) ^ r := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (by omega : m ≤ 33 * r)) r
  refine h1.trans ?_
  rw [div_le_iff₀ hf]
  calc (m:ℝ)^r ≤ (33:ℝ)^r * (r:ℝ)^r := hm
    _ ≤ (33:ℝ)^r * (Real.exp r * r.factorial) := by gcongr
    _ = (33:ℝ)^r * Real.exp 1 ^ r * r.factorial := by rw [he]; ring
    _ ≤ (33:ℝ)^r * 3 ^ r * r.factorial := by gcongr
    _ ≤ (128:ℝ)^r * r.factorial := by
        rw [← mul_pow]; gcongr; norm_num

theorem big (m k q : ℕ) (hk : 33 ≤ k) (hkm : k * k ≤ m) (hq : q ≤ k + 1) :
    2 ^ (4 * q) ≤ Nat.choose m k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hp : (((m + 1 - (j+1) : ℕ) : ℝ)) ^ (j+1) / ((j+1).factorial : ℝ) ≤ (m.choose (j+1) : ℝ) :=
    Nat.pow_le_choose (j+1) m
  have a1 : 2 ^ (4 * q) ≤ j ^ (j+1) := by
    have h16 : 16 ≤ 2 ^ (j+1) := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (j+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 ^ (4 * q) ≤ 2 ^ (4 * (j+2)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 16 ^ (j+1) * 16 := by rw [pow_mul, ← pow_succ]; norm_num
      _ ≤ 16 ^ (j+1) * 2 ^ (j+1) := Nat.mul_le_mul_left _ h16
      _ = 32 ^ (j+1) := by rw [← mul_pow]; norm_num
      _ ≤ j ^ (j+1) := Nat.pow_le_pow_left (by omega) _
  have a2 : (j+1).factorial ≤ (j+1) ^ (j+1) := Nat.factorial_le_pow (j+1)
  have a3 : (j+1) * j ≤ m + 1 - (j+1) := by
    apply Nat.le_sub_of_add_le
    have : (j+1) * (j+1) = (j+1) * j + (j+1) := by ring
    omega
  have a4 : 2 ^ (4 * q) * (j+1).factorial ≤ (m + 1 - (j+1)) ^ (j+1) := by
    calc 2 ^ (4 * q) * (j+1).factorial ≤ j ^ (j+1) * (j+1) ^ (j+1) := Nat.mul_le_mul a1 a2
      _ = (j * (j+1)) ^ (j+1) := by rw [mul_pow]
      _ ≤ _ := Nat.pow_le_pow_left (by nlinarith) _
  have hf : (0:ℝ) < ((j+1).factorial : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos _)
  have : ((2 ^ (4 * q) : ℕ) : ℝ) ≤ (m.choose (j+1) : ℝ) := by
    refine le_trans ?_ hp
    rw [le_div_iff₀ hf]
    exact_mod_cast a4
  exact_mod_cast this

end RandOnlineSetCoverSqrt.Dev.L35

namespace RandOnlineSetCoverSqrt.LowerBound
open RandOnlineSetCoverSqrt.Dev.L35

theorem chk_lemma_3_5 :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∃ C : Family m,
      C.card = familySize m ∧ UnionExpanding (kParam m) (qParam m) (rParam m) C := by
  refine ⟨1089, fun m hm => ?_⟩
  set k := kParam m with hk
  set q := qParam m with hq
  set r := rParam m with hr
  have hkdef : k = ⌊Real.sqrt (m:ℝ)⌋₊ := rfl
  have hqdef : q = ⌈Real.sqrt (m:ℝ)⌉₊ := rfl
  have hsq : Real.sqrt (m:ℝ) < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsq2 : (k : ℝ) ≤ Real.sqrt (m:ℝ) := Nat.floor_le (Real.sqrt_nonneg _)
  have hk2 : k * k ≤ m := by
    have : (k:ℝ) * k ≤ m := by
      calc (k:ℝ) * k ≤ Real.sqrt m * Real.sqrt m := by gcongr
        _ = m := Real.mul_self_sqrt (Nat.cast_nonneg _)
    exact_mod_cast this
  have hk3 : m < (k+1) * (k+1) := by
    have : (m:ℝ) < ((k:ℝ)+1) * ((k:ℝ)+1) := by
      calc (m:ℝ) = Real.sqrt m * Real.sqrt m := (Real.mul_self_sqrt (Nat.cast_nonneg _)).symm
        _ < ((k:ℝ)+1) * ((k:ℝ)+1) := by gcongr
    exact_mod_cast this
  have hk32 : 33 ≤ k := by
    by_contra hlt
    push Not at hlt
    have : (k+1)*(k+1) ≤ 33*33 := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hqk : k ≤ q := by
    have : (k:ℝ) ≤ q := hsq2.trans (Nat.le_ceil _)
    exact_mod_cast this
  have hqk1 : q ≤ k + 1 := by
    rw [hqdef]; apply Nat.ceil_le.mpr; exact hsq.le.trans (by simp)
  have hr32 : 32 * r ≤ m := by simp [hr, rParam]; omega
  have hr33 : m < 32 * (r + 1) := by simp [hr, rParam]; omega
  have hkr : k ≤ r := by
    have : k * k ≤ 32 * r + 31 := by omega
    by_contra hlt
    push Not at hlt
    nlinarith
  have hrm : r ≤ m := by omega
  have hr31 : 31 ≤ r := by omega
  have hMN : 2 ^ (4 * q) ≤ Nat.choose m k := big m k q (by omega) hk2 hqk1
  have hfirst : (Nat.choose (2 ^ (4 * q)) q : ℝ) * (Nat.choose m r : ℝ) *
      ((Nat.choose r k : ℝ) / (Nat.choose m k : ℝ)) ^ q < 1 := by
    have hNpos : (0:ℝ) < Nat.choose m k := by exact_mod_cast Nat.choose_pos (by omega : k ≤ m)
    have hA : (Nat.choose (2 ^ (4 * q)) q : ℝ) ≤ 2 ^ (4 * q * q) := by
      have := Nat.choose_le_pow (2 ^ (4 * q)) q
      calc _ ≤ (((2 ^ (4 * q)) ^ q : ℕ) : ℝ) := by exact_mod_cast this
        _ = 2 ^ (4 * q * q) := by push_cast; rw [← pow_mul]
    have hB : (Nat.choose m r : ℝ) ≤ 2 ^ (7 * r) := by
      have := choose_le_128 m r hr31 (by omega)
      calc _ ≤ (128:ℝ) ^ r := this
        _ = 2 ^ (7 * r) := by rw [pow_mul]; norm_num
    have hC : (Nat.choose r k : ℝ) / (Nat.choose m k : ℝ) ≤ (1/32 : ℝ) ^ k := by
      rw [div_le_iff₀ hNpos]
      have h := choose_ratio r m k hrm
      have h' : (Nat.choose r k : ℝ) * (m:ℝ) ^ k ≤ (r:ℝ) ^ k * Nat.choose m k := by exact_mod_cast h
      have hmpos : (0:ℝ) < (m:ℝ) ^ k := by positivity
      have hrm' : (r:ℝ) ^ k ≤ ((1/32:ℝ) ^ k) * (m:ℝ) ^ k := by
        rw [← mul_pow]; apply pow_le_pow_left₀ (Nat.cast_nonneg _)
        have : (32:ℝ) * r ≤ m := by exact_mod_cast hr32
        linarith
      have : (Nat.choose r k : ℝ) * (m:ℝ) ^ k ≤ ((1/32:ℝ) ^ k * Nat.choose m k) * (m:ℝ) ^ k := by
        calc _ ≤ (r:ℝ) ^ k * Nat.choose m k := h'
          _ ≤ ((1/32:ℝ) ^ k * (m:ℝ) ^ k) * Nat.choose m k := by gcongr
          _ = _ := by ring
      exact le_of_mul_le_mul_right this hmpos
    have hC' : ((Nat.choose r k : ℝ) / (Nat.choose m k : ℝ)) ^ q ≤ (1/32:ℝ) ^ (k * q) := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (by positivity) hC q
    have hexp : 4 * q * q + 7 * r < 5 * (k * q) := by
      have h7 : 32 * (7 * r) ≤ 7 * m := by omega
      nlinarith
    calc (Nat.choose (2 ^ (4 * q)) q : ℝ) * (Nat.choose m r : ℝ) *
          ((Nat.choose r k : ℝ) / (Nat.choose m k : ℝ)) ^ q
        ≤ 2 ^ (4 * q * q) * 2 ^ (7 * r) * (1/32:ℝ) ^ (k * q) := by gcongr
      _ = 2 ^ (4 * q * q + 7 * r) * (1/32:ℝ) ^ (k * q) := by rw [pow_add]
      _ < 32 ^ (k * q) * (1/32:ℝ) ^ (k * q) := by
          gcongr
          calc (2:ℝ) ^ (4 * q * q + 7 * r) < 2 ^ (5 * (k * q)) :=
                pow_lt_pow_right₀ (by norm_num) hexp
            _ = 32 ^ (k * q) := by rw [pow_mul]; norm_num
      _ = 1 := by rw [← mul_pow]; norm_num
  have := lemma_3_3 m k q r (2 ^ (4 * q)) (by omega) hkr hrm (by omega) hMN hfirst
  simpa [familySize] using this

end RandOnlineSetCoverSqrt.LowerBound
end

theorem solution : type_of% @RandOnlineSetCoverSqrt.LowerBound.chk_lemma_3_5 := @RandOnlineSetCoverSqrt.LowerBound.chk_lemma_3_5
