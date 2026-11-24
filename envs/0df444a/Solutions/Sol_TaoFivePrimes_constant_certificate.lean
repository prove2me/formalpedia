-- Prove2me | solution 1 for TaoFivePrimes.constant_certificate
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-29T13:24:24.728662+00:00
-- url     : https://prove2.me/submissions/94da0ffd-f8c4-4e6c-82d3-29cdfe91270c

import Mathlib
import Definitions.Def_TaoFivePrimes_mertens_cert_511_tables
import Theorems.Thm_TaoFivePrimes_WLO512_le_sum512
import Theorems.Thm_TaoFivePrimes_mertens_tail_upper_bound
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false

namespace TaoFivePrimes

private lemma primesLE_succ (k : Nat) :
    Nat.primesLE (k+1) = if (k+1).Prime then insert (k+1) (Nat.primesLE k) else Nat.primesLE k := by
  ext p
  rw [Nat.mem_primesLE]
  by_cases h : (k+1).Prime
  · rw [if_pos h, Finset.mem_insert, Nat.mem_primesLE]
    constructor
    · intro hp
      rcases eq_or_lt_of_le hp.1 with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr ⟨by omega, hp.2⟩
    · rintro (rfl | ⟨hle, hpr⟩)
      · exact ⟨le_refl _, h⟩
      · exact ⟨by omega, hpr⟩
  · rw [if_neg h, Nat.mem_primesLE]
    constructor
    · intro hp
      have hne : p ≠ k+1 := fun he => h (he ▸ hp.2)
      exact ⟨by omega, hp.2⟩
    · intro hp; exact ⟨by omega, hp.2⟩


private lemma sum_primesLE_succ {α : Type*} [AddCommMonoid α] (k : Nat) (f : Nat → α) :
    ∑ p ∈ Nat.primesLE (k+1), f p = ∑ p ∈ Nat.primesLE k, f p + if (k+1).Prime then f (k+1) else 0 := by
  rw [primesLE_succ k]
  by_cases h : (k+1).Prime
  · rw [if_pos h, if_pos h, Finset.sum_insert]
    · rw [add_comm]
    · simp only [Nat.mem_primesLE]; omega
  · rw [if_neg h, if_neg h, add_zero]
private lemma loglog_mono {a b : Real} (ha : 1 < a) (h : a ≤ b) :
    Real.log (Real.log a) ≤ Real.log (Real.log b) :=
  Real.log_le_log (Real.log_pos ha) (Real.log_le_log (by linarith) h)


private lemma log_ge_one_sub_inv {x : Real} (hx : 0 < x) : 1 - 1/x ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (show (0:Real) < x⁻¹ by positivity)
  rw [Real.log_inv] at h
  rw [one_div]
  linarith


private lemma neg_log_sub_le (x : Real) (hx0 : 0 < x) (hx : x ≤ 1/4) :
    -Real.log (1 - x) - x ≤ x^2/(2*(1-x)) := by
  have hx1 : |x| < 1 := by rw [abs_of_pos hx0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le (x := x) hx1 3
  obtain ⟨hlow, -⟩ := abs_le.mp h
  have herr : |x|^4/(1 - |x|) ≤ x^4/(1-x) := by rw [abs_of_pos hx0]
  have hsum : (∑ i ∈ Finset.range 3, x^(i+1)/(i+1)) = x + x^2/2 + x^3/3 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  have h2 : -Real.log (1-x) - x ≤ x^2/2 + x^3/3 + x^4/(1-x) := by
    rw [hsum] at hlow
    have := le_trans (neg_le_neg herr) hlow
    linarith
  have h3 : x^2/2 + x^3/3 + x^4/(1-x) ≤ x^2/(2*(1-x)) := by
    rw [le_div_iff₀ (by linarith : (0:Real) < 2*(1-x))]
    have hd0 : (1:Real) - x ≠ 0 := by linarith
    have h1 : x^4/(1-x) * (2*(1-x)) = 2*x^4 := by
      field_simp
    have h2 : x^2/2 * (2*(1-x)) = x^2*(1-x) := by
      field_simp
    have h3 : x^3/3 * (2*(1-x)) = (2/3)*x^3*(1-x) := by
      field_simp
    rw [add_mul, add_mul, h1, h2, h3]
    have h4x : (4:Real)*x - 1 ≤ 0 := by linarith
    nlinarith [hx0, hx, mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hx0.le 3) h4x]
  linarith
private lemma w_ge_small (p : Nat) (hp : 4 ≤ p) :
    -(1/(2*(p:Real)*((p:Real)-1))) ≤ Real.log (1 - 1/(p:Real)) + 1/(p:Real) := by
  have hp0 : (0:Real) < (p:Real) := by positivity
  have hp4 : (4:Real) ≤ (p:Real) := by exact_mod_cast hp
  have hx0 : 0 < 1/(p:Real) := by positivity
  have hx : 1/(p:Real) ≤ 1/4 := by
    rw [div_le_iff₀ hp0]
    linarith
  have h := neg_log_sub_le (1/(p:Real)) hx0 hx
  have hpne : (p:Real) ≠ 0 := ne_of_gt hp0
  have hp1ne : (p:Real) - 1 ≠ 0 := by
    have : (1:Real) < (p:Real) := by linarith
    linarith
  have hx1ne : (1:Real) - 1/(p:Real) ≠ 0 := by
    have : 1/(p:Real) < 1 := by
      rw [div_lt_one hp0]
      linarith
    linarith
  have hxeq : (1/(p:Real))^2/(2*(1-1/(p:Real))) = 1/(2*(p:Real)*((p:Real)-1)) := by
    field_simp
  rw [hxeq] at h
  linarith
private lemma WLOi_512 : WLOi 512 = -315600119 := by decide

private lemma WLO_512_val : WLO 512 = (-315600119/1000000000) := by
  rw [WLO, WLOi_512]
  norm_num
private lemma gamma_ge_glo : glo ≤ Real.eulerMascheroniConstant := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 1024
  rw [Real.eulerMascheroniSeq] at h
  norm_num at h
  have hH : (300367/40000 : Real) ≤ (harmonic 1024 : Real) := by norm_num [harmonic]
  have hlog : Real.log 1025 ≤ 10 * (6931471808/10000000000 : Real) + 1/1024 := by
    have hsplit : Real.log 1025 = 10 * Real.log 2 + Real.log (1 + 1/1024) := by
      rw [show (1025:Real) = 2^10 * (1 + 1/1024) by norm_num,
          Real.log_mul (by positivity) (by positivity), Real.log_pow]
      ring
    have h2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have h3 : Real.log (1 + 1/1024) ≤ 1/1024 := by
      have := Real.log_le_sub_one_of_pos (show (0:Real) < 1 + 1/1024 by norm_num)
      linarith
    linarith
  have hglo : glo = 300367/40000 - 10 * (6931471808/10000000000 : Real) - 1/1024 := by
    unfold glo
    norm_num
  linarith
private lemma hmid :
    -(1/2)*(1/512 - 1/8192) ≤
      ∑ p ∈ Nat.primesLE 8192 \ Nat.primesLE 512, (Real.log (1 - 1/(p:Real)) + 1/(p:Real)) := by
  have hpt : ∀ p ∈ Nat.primesLE 8192 \ Nat.primesLE 512,
      -(1/(2*(p:Real)*((p:Real)-1))) ≤ Real.log (1 - 1/(p:Real)) + 1/(p:Real) := by
    intro p hp
    rw [Finset.mem_sdiff] at hp
    have hle1 : ¬ p ≤ 512 := fun h => hp.2 (by rw [Nat.mem_primesLE]; exact ⟨h, (Nat.mem_primesLE.mp hp.1).2⟩)
    have := (Nat.mem_primesLE.mp hp.1).1
    exact w_ge_small p (by omega)
  have hneg : ∑ p ∈ Nat.primesLE 8192 \ Nat.primesLE 512, -(Real.log (1 - 1/(p:Real)) + 1/(p:Real)) ≤
      (1/2) * ∑ n ∈ Finset.Ico (513:Nat) 8193, 1/((n:Real)*((n:Real)-1)) := by
    calc ∑ p ∈ Nat.primesLE 8192 \ Nat.primesLE 512, -(Real.log (1 - 1/(p:Real)) + 1/(p:Real))
        ≤ ∑ p ∈ Nat.primesLE 8192 \ Nat.primesLE 512, 1/(2*(p:Real)*((p:Real)-1)) :=
          Finset.sum_le_sum (fun p hp => by linarith [hpt p hp])
      _ ≤ ∑ n ∈ Finset.Ico (513:Nat) 8193, 1/(2*(n:Real)*((n:Real)-1)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            rw [Finset.mem_sdiff, Nat.mem_primesLE] at hp
            have hp512 : ¬ p ≤ 512 := fun h => hp.2 (by rw [Nat.mem_primesLE]; exact ⟨h, hp.1.2⟩)
            have hp8192 : p ≤ 8192 := hp.1.1
            rw [Finset.mem_Ico]
            omega
          · intro n hn hnnot
            have hn513 : 513 ≤ n := (Finset.mem_Ico.mp hn).1
            have hn0 : (0:Real) < (n:Real) := by exact_mod_cast (by omega : 0 < n)
            have hn1 : (0:Real) < (n:Real) - 1 := by
              have : (1:Real) < (n:Real) := by exact_mod_cast (by omega : 1 < n)
              linarith
            positivity
      _ = (1/2) * ∑ n ∈ Finset.Ico (513:Nat) 8193, 1/((n:Real)*((n:Real)-1)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          have hn513 : 513 ≤ n := (Finset.mem_Ico.mp hn).1
          have hn0 : (n:Real) ≠ 0 := by
            have : (0:Real) < (n:Real) := by exact_mod_cast (by omega : 0 < n)
            linarith
          have hn1 : (n:Real) - 1 ≠ 0 := by
            have : (1:Real) < (n:Real) := by exact_mod_cast (by omega : 1 < n)
            linarith
          field_simp
  have hterm : ∀ n ∈ Finset.Ico (513:Nat) 8193,
      1/((n:Real)*((n:Real)-1)) = 1/((n:Real)-1) - 1/(n:Real) := by
    intro n hn
    have hn513 : 513 ≤ n := (Finset.mem_Ico.mp hn).1
    have h2 : (2:Real) ≤ (n:Real) := by exact_mod_cast (by omega : 2 ≤ n)
    have hn0 : (n:Real) ≠ 0 := ne_of_gt (by linarith)
    have hn1 : (n:Real) - 1 ≠ 0 := ne_of_gt (by linarith)
    field_simp
    ring
  have htel2 : ∀ k, ∑ n ∈ Finset.Ico (513:Nat) (513 + k), (1/((n:Real)-1) - 1/(n:Real)) =
      1/512 - 1/((512 + k : Nat) : Real) := by
    intro k
    induction k with
    | zero => simp
    | succ j ih =>
        rw [show 513 + (j+1) = (513 + j) + 1 by omega,
            Finset.sum_Ico_succ_top (by omega : 513 ≤ 513 + j) (fun n => 1/((n:Real)-1) - 1/(n:Real)),
            ih]
        push_cast
        ring
  have htel : ∑ n ∈ Finset.Ico (513:Nat) 8193, 1/((n:Real)*((n:Real)-1)) = 1/512 - 1/8192 := by
    calc ∑ n ∈ Finset.Ico (513:Nat) 8193, 1/((n:Real)*((n:Real)-1))
        = ∑ n ∈ Finset.Ico (513:Nat) 8193, (1/((n:Real)-1) - 1/(n:Real)) :=
          Finset.sum_congr rfl (fun n hn => hterm n hn)
      _ = 1/512 - 1/8192 := by
          rw [show (8193:Nat) = 513 + 7680 by norm_num, htel2 7680]
          norm_num
  rw [Finset.sum_neg_distrib, htel] at hneg
  linarith
private lemma tlo_le_Tinf :
    tlo ≤ ∑' p : Nat.Primes, (Real.log (1 - 1/(p:Real)) + 1/(p:Real)) := by
  have hP2 : (∑ p ∈ Nat.primesLE 8192, (Real.log (1 - 1/(p:Real)) + 1/(p:Real))) ≤
      (∑' p : Nat.Primes, (Real.log (1 - 1/(p:Real)) + 1/(p:Real))) + 1/(8192:Real) := by
    have h := mertens_tail_upper_bound (x := (8192:Real)) (by norm_num)
    convert h using 1
    · norm_num
    · norm_num
  have hsub : Nat.primesLE 512 ⊆ Nat.primesLE 8192 := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hsplit : ∑ p ∈ Nat.primesLE 8192, (Real.log (1 - 1/(p:Real)) + 1/(p:Real)) =
      ∑ p ∈ Nat.primesLE 512, (Real.log (1 - 1/(p:Real)) + 1/(p:Real)) +
      ∑ p ∈ Nat.primesLE 8192 \ Nat.primesLE 512, (Real.log (1 - 1/(p:Real)) + 1/(p:Real)) := by
    rw [← Finset.sum_sdiff hsub, add_comm]
  have hW := WLO512_le_sum512
  have hm := hmid
  unfold tlo
  linarith
private lemma M_le_glo_tlo : M ≤ glo + tlo := by
  have h1 : (WLO 512 : Real) = ((-315600119/1000000000) : Real) := by
    have hq := WLO_512_val
    exact_mod_cast hq
  unfold M Mq glo tlo
  rw [h1]
  norm_num

theorem constant_certificate :
    (Mq : Real) ≤ Real.eulerMascheroniConstant +
      ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : Real)) + 1 / (p : Real)) := by
  have hM : (Mq : Real) ≤ glo + tlo := M_le_glo_tlo
  linarith [gamma_ge_glo, tlo_le_Tinf]

end TaoFivePrimes

open TaoFivePrimes

theorem solution :
    (Mq : Real) ≤ Real.eulerMascheroniConstant +
      ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : Real)) + 1 / (p : Real)) :=
  TaoFivePrimes.constant_certificate
