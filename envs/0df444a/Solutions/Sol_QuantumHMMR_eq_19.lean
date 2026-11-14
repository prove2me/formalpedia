-- Prove2me | solution 1 for QuantumHMMR.eq_19
-- status  : ACCEPTED   (prove)
-- author  : @Jesko
-- created : 2026-11-13T15:50:31.226199+00:00
-- url     : https://prove2.me/submissions/1e094f84-4454-49b0-88e5-3932cc8a082e

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Definitions.Def_QuantumHMMR_logSq

set_option autoImplicit false
open Finset

private lemma binom_gen (T : ℕ) (p q z : ℝ) :
    ∑ k ∈ range (T + 1), (T.choose k : ℝ) * p ^ k * q ^ (T-k) * z ^ k =
      (p*z+q)^T := by
  rw [add_pow]
  apply sum_congr rfl
  intro k hk
  rw [mul_pow]
  ring

private lemma binom_mean (T : ℕ) (p : ℝ) :
    ∑ k ∈ range (T+1), (k : ℝ) * (T.choose k : ℝ) * p^k * (1-p)^(T-k) = T*p := by
  cases T with
  | zero => simp
  | succ n =>
    rw [sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    calc
      ∑ k ∈ range (n+1), ((k+1 : ℕ) : ℝ) * ((n+1).choose (k+1) : ℝ) *
          p^(k+1) * (1-p)^((n+1)-(k+1)) =
        ((n+1 : ℕ) : ℝ) * p *
          ∑ k ∈ range (n+1), (n.choose k : ℝ) * p^k * (1-p)^(n-k) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro k hk
        have hc : ((k+1 : ℕ) : ℝ) * ((n+1).choose (k+1) : ℝ) =
            ((n+1 : ℕ) : ℝ) * (n.choose k : ℝ) := by
          simpa [mul_comm] using (congrArg (fun a : ℕ => (a : ℝ)) (Nat.add_one_mul_choose_eq n k)).symm
        rw [hc, Nat.add_sub_add_right, pow_succ]
        ring
      _ = ((n+1 : ℕ) : ℝ) * p := by
        have h := binom_gen n p (1-p) 1
        simp only [one_pow, mul_one] at h
        rw [show p + (1-p) = 1 by ring, one_pow] at h
        rw [h, mul_one]

private lemma binom_tail (T m : ℕ) (hm : 2 ≤ m) :
    ∑ k ∈ (range (T+1)).filter (fun k => 2*T < k*m),
       (T.choose k : ℝ) * ((m : ℝ)⁻¹)^k * (1-(m : ℝ)⁻¹)^(T-k)
    ≤ (Real.exp 1 / 4)^((T : ℝ)/m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hp0 : 0 ≤ (m : ℝ)⁻¹ := le_of_lt (inv_pos.mpr hm0)
  have hp1 : (m : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hm0).mpr hm1
  let w : ℕ → ℝ := fun k => (T.choose k : ℝ) * ((m : ℝ)⁻¹)^k *
    (1-(m : ℝ)⁻¹)^(T-k)
  have hw : ∀ k, 0 ≤ w k := fun k => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
    (pow_nonneg (sub_nonneg.mpr hp1) _)
  have ha : 0 < (2 : ℝ) ^ (2 * ((T : ℝ)/m)) := Real.rpow_pos_of_pos (by norm_num) _
  have hmark : (2 : ℝ) ^ (2*((T : ℝ)/m)) *
      ∑ k ∈ (range (T+1)).filter (fun k => 2*T < k*m), w k ≤ (1+(m : ℝ)⁻¹)^T := by
    calc
      _ ≤ ∑ k ∈ (range (T+1)).filter (fun k => 2*T < k*m), w k * (2:ℝ)^k := by
        rw [mul_sum]
        apply sum_le_sum
        intro k hk
        have hk' : 2 * ((T : ℝ)/m) ≤ k := by
          have h : (2:ℝ)*T < (k:ℝ)*m := by exact_mod_cast (mem_filter.mp hk).2
          rw [← mul_div_assoc]
          exact (div_le_iff₀ hm0).mpr (le_of_lt h)
        have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hk'
        rw [Real.rpow_natCast] at hpow
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hpow (hw k)
      _ ≤ ∑ k ∈ range (T+1), w k * (2:ℝ)^k := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro k hk hnot
        exact mul_nonneg (hw k) (by positivity)
      _ = (1+(m : ℝ)⁻¹)^T := by
        dsimp [w]
        rw [binom_gen]
        congr 1
        ring
  have hexp : (1+(m : ℝ)⁻¹)^T ≤ Real.exp ((T : ℝ)/m) := by
    calc
      _ ≤ (Real.exp ((m : ℝ)⁻¹))^T := by
        apply pow_le_pow_left₀ (by positivity)
        linarith [Real.add_one_le_exp ((m : ℝ)⁻¹)]
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1
  have hbound : (∑ k ∈ (range (T+1)).filter (fun k => 2*T < k*m), w k) ≤
      Real.exp ((T:ℝ)/m) / (2:ℝ)^(2*((T:ℝ)/m)) := by
    apply (le_div_iff₀ ha).mpr
    rw [mul_comm]
    exact le_trans hmark hexp
  have heq : Real.exp ((T : ℝ)/m) / (2:ℝ)^(2*((T:ℝ)/m)) =
      (Real.exp 1 / 4)^((T:ℝ)/m) := by
    rw [Real.rpow_def_of_pos (by positivity : (0:ℝ) < Real.exp 1 / 4),
      Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), ← Real.exp_sub]
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (by norm_num), Real.log_exp]
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    rw [hlog4]
    congr 1
    ring
  exact heq ▸ hbound

 theorem solution :
    (∀ m T : ℕ, 2 ≤ m →
      ∑ k ∈ Finset.range (T + 1),
          (k : ℝ) * (T.choose k : ℝ) * ((m : ℝ)⁻¹) ^ k * (1 - (m : ℝ)⁻¹) ^ (T - k) = T / m ∧
      ∑ k ∈ (Finset.range (T + 1)).filter (fun k => 2 * T < k * m),
          (T.choose k : ℝ) * ((m : ℝ)⁻¹) ^ k * (1 - (m : ℝ)⁻¹) ^ (T - k)
        ≤ (Real.exp 1 / 4) ^ ((T : ℝ) / m)) ∧
    ∀ β : ℝ, 1 < β → ∃ c : ℝ, 0 < c ∧ ∀ m n : ℕ, 2 ≤ m →
      (Real.exp 1 / 4) ^ (((3 * m * ⌈QuantumHMMR.logSq β n⌉₊ : ℕ) : ℝ) / m) ≤
        Real.exp (-(c * QuantumHMMR.logSq β n)) := by
  constructor
  · intro m T hm
    exact ⟨by simpa [div_eq_mul_inv] using binom_mean T (m:ℝ)⁻¹, binom_tail T m hm⟩
  · intro β hβ
    have hlog : 1 < Real.log 4 := by
      apply (Real.lt_log_iff_exp_lt (by norm_num)).mpr
      exact lt_trans Real.exp_one_lt_d9 (by norm_num)
    refine ⟨3 * (Real.log 4 - 1), by positivity, ?_⟩
    intro m n hm
    have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    have hceil : QuantumHMMR.logSq β n ≤ (⌈QuantumHMMR.logSq β n⌉₊ : ℝ) := Nat.le_ceil _
    rw [Real.rpow_def_of_pos (by positivity : (0:ℝ) < Real.exp 1 / 4)]
    apply Real.exp_le_exp.mpr
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (by norm_num), Real.log_exp]
    have hcast : (((3*m*⌈QuantumHMMR.logSq β n⌉₊ : ℕ) : ℝ) / m) =
        3 * (⌈QuantumHMMR.logSq β n⌉₊ : ℝ) := by
      push_cast
      field_simp
    rw [hcast]
    nlinarith
