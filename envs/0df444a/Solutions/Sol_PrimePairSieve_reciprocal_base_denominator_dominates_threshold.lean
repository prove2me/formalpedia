-- Prove2me | solution 1 for PrimePairSieve.reciprocal_base_denominator_dominates_threshold
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-23T14:13:18.161886+00:00
-- url     : https://prove2.me/submissions/b05d63be-7821-4894-a3bc-1a6e92096320
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PrimePairSieve_reciprocal_base_denominator_quadratic_expansion_sharp
import Theorems.Thm_PrimePairSieve_sieve_constants_certificate
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

open scoped BigOperators

set_option maxHeartbeats 1000000

private lemma log_le_fourth_root (t : ℝ) (ht : 0 < t) :
    Real.log t ≤ 4 * t ^ (1 / 4 : ℝ) / Real.exp 1 := by
  have ht0 : 0 ≤ t := ht.le
  have hroot : (t ^ (1 / 4 : ℝ)) ^ 4 = t := by
    rw [show (1 / 4 : ℝ) = ((4 : ℕ)⁻¹ : ℝ) by norm_num]
    exact Real.rpow_inv_natCast_pow ht0 (by norm_num)
  have hlog_eq : Real.log t = 4 * Real.log (t ^ (1 / 4 : ℝ)) := by
    conv_lhs => rw [← hroot]
    rw [Real.log_pow]
    norm_num
  have hpos : 0 < t ^ (1 / 4 : ℝ) / Real.exp 1 := by positivity
  have hsub := Real.log_le_sub_one_of_pos hpos
  rw [Real.log_div (ne_of_gt (Real.rpow_pos_of_pos ht _)) (Real.exp_ne_zero 1),
    Real.log_exp] at hsub
  have hle : Real.log (t ^ (1 / 4 : ℝ)) ≤ t ^ (1 / 4 : ℝ) / Real.exp 1 := by linarith
  calc Real.log t = 4 * Real.log (t ^ (1 / 4 : ℝ)) := hlog_eq
    _ ≤ 4 * (t ^ (1 / 4 : ℝ) / Real.exp 1) := by linarith
    _ = 4 * t ^ (1 / 4 : ℝ) / Real.exp 1 := by ring

private lemma sieve_f_bound (z : ℝ) (hz : 40 ≤ z) :
    (z + 1) * (Real.log (4 * z)) ^ 2 / z ^ 2 ≤ 0.7024 := by
  have hz0 : 0 < z := by linarith
  have ht : 0 < 4 * z := by positivity
  have hlogb : Real.log (4 * z) ≤ 4 * (4 * z) ^ (1 / 4 : ℝ) / Real.exp 1 := by
    have hroot : ((4 * z) ^ (1 / 4 : ℝ)) ^ 4 = 4 * z := by
      rw [show (1 / 4 : ℝ) = ((4 : ℕ)⁻¹ : ℝ) by norm_num]
      exact Real.rpow_inv_natCast_pow ht.le (by norm_num)
    have hlog_eq : Real.log (4 * z) = 4 * Real.log ((4 * z) ^ (1 / 4 : ℝ)) := by
      conv_lhs => rw [← hroot]
      rw [Real.log_pow]
      norm_num
    have hpos : 0 < (4 * z) ^ (1 / 4 : ℝ) / Real.exp 1 := by positivity
    have hsub := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_div (ne_of_gt (Real.rpow_pos_of_pos ht _)) (Real.exp_ne_zero 1),
      Real.log_exp] at hsub
    have hle : Real.log ((4 * z) ^ (1 / 4 : ℝ)) ≤ (4 * z) ^ (1 / 4 : ℝ) / Real.exp 1 := by
      linarith
    calc Real.log (4 * z) = 4 * Real.log ((4 * z) ^ (1 / 4 : ℝ)) := hlog_eq
      _ ≤ 4 * ((4 * z) ^ (1 / 4 : ℝ) / Real.exp 1) := by linarith
      _ = 4 * (4 * z) ^ (1 / 4 : ℝ) / Real.exp 1 := by ring
  have hlogpos : 0 ≤ Real.log (4 * z) := Real.log_nonneg (by linarith)
  have hsq : (Real.log (4 * z)) ^ 2 ≤ (4 * (4 * z) ^ (1 / 4 : ℝ) / Real.exp 1) ^ 2 :=
    pow_le_pow_left₀ hlogpos hlogb 2
  have hroot2 : ((4 * z) ^ (1 / 4 : ℝ)) ^ 2 = 2 * Real.sqrt z := by
    have h1 : ((4 * z) ^ (1 / 4 : ℝ)) ^ 2 = (4 * z) ^ (1 / 2 : ℝ) := by
      rw [sq, ← Real.rpow_add ht (1 / 4 : ℝ) (1 / 4 : ℝ)]
      norm_num
    have h2 : (4 * z) ^ (1 / 2 : ℝ) = 2 * Real.sqrt z := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      have h4 : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      rw [h4]
    rw [h1, h2]
  have hrhs : (4 * (4 * z) ^ (1 / 4 : ℝ) / Real.exp 1) ^ 2
      = 32 * Real.sqrt z / (Real.exp 1) ^ 2 := by
    rw [div_pow, mul_pow, hroot2]
    ring
  have hone : (z + 1) * (Real.log (4 * z)) ^ 2 / z ^ 2
      ≤ (z + 1) * (32 * Real.sqrt z / (Real.exp 1) ^ 2) / z ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [← hrhs]
    exact mul_le_mul_of_nonneg_left hsq (by linarith)
  have he2 : (7.389 : ℝ) ≤ (Real.exp 1) ^ 2 := by
    calc (7.389 : ℝ) ≤ (2.7182818283 : ℝ) ^ 2 := by norm_num
      _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 2
  have hsqrtz : (6.32 : ℝ) ≤ Real.sqrt z := by
    calc (6.32 : ℝ) = Real.sqrt (6.32 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 40 := Real.sqrt_le_sqrt (by norm_num)
      _ ≤ Real.sqrt z := Real.sqrt_le_sqrt hz
  have hzdiv : Real.sqrt z ≤ z / 6.32 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 6.32)]
    calc Real.sqrt z * 6.32 ≤ Real.sqrt z * Real.sqrt z :=
          mul_le_mul_of_nonneg_left hsqrtz (Real.sqrt_nonneg z)
      _ = z := by rw [← sq]; exact Real.sq_sqrt hz0.le
  have hone2 : (z + 1) * Real.sqrt z ≤ (1.025 / 6.32) * z ^ 2 := by
    have h1 : (z + 1) * Real.sqrt z ≤ (z + 1) * (z / 6.32) :=
      mul_le_mul_of_nonneg_left hzdiv (by linarith)
    have h4 : z + 1 ≤ 1.025 * z := by nlinarith [hz]
    have h5 : (z + 1) * (z / 6.32) ≤ (1.025 / 6.32) * z ^ 2 := by
      rw [show (z + 1) * (z / 6.32) = (z + 1) * z / 6.32 by ring]
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 6.32)]
      nlinarith [mul_le_mul_of_nonneg_right h4 hz0.le]
    linarith
  have hmid : (z + 1) * (32 * Real.sqrt z / (Real.exp 1) ^ 2) / z ^ 2
      ≤ (32 / 7.389) * (1.025 / 6.32) := by
    have heq : (z + 1) * (32 * Real.sqrt z / (Real.exp 1) ^ 2) / z ^ 2
        = (32 / (Real.exp 1) ^ 2) * ((z + 1) * Real.sqrt z / z ^ 2) := by ring
    rw [heq]
    have hf1 : (32 : ℝ) / (Real.exp 1) ^ 2 ≤ 32 / 7.389 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) he2
    have hz2 : (z + 1) * Real.sqrt z / z ^ 2 ≤ 1.025 / 6.32 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
      exact hone2
    exact mul_le_mul hf1 hz2 (by positivity) (by positivity)
  have hnum : (32 / 7.389) * (1.025 / 6.32) ≤ (0.7024 : ℝ) := by norm_num
  linarith [hone, hmid, hnum]

private lemma sieve_g_bound (z : ℝ) (hz : 40 ≤ z) :
    (z + 1) * (Real.log (4 * z)) ^ 4 / z ^ 2 ≤ 19.227 := by
  have hz0 : 0 < z := by linarith
  have ht : 0 < 4 * z := by positivity
  have hlogb : Real.log (4 * z) ≤ 4 * (4 * z) ^ (1 / 4 : ℝ) / Real.exp 1 := by
    have hroot : ((4 * z) ^ (1 / 4 : ℝ)) ^ 4 = 4 * z := by
      rw [show (1 / 4 : ℝ) = ((4 : ℕ)⁻¹ : ℝ) by norm_num]
      exact Real.rpow_inv_natCast_pow ht.le (by norm_num)
    have hlog_eq : Real.log (4 * z) = 4 * Real.log ((4 * z) ^ (1 / 4 : ℝ)) := by
      conv_lhs => rw [← hroot]
      rw [Real.log_pow]
      norm_num
    have hpos : 0 < (4 * z) ^ (1 / 4 : ℝ) / Real.exp 1 := by positivity
    have hsub := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_div (ne_of_gt (Real.rpow_pos_of_pos ht _)) (Real.exp_ne_zero 1),
      Real.log_exp] at hsub
    have hle : Real.log ((4 * z) ^ (1 / 4 : ℝ)) ≤ (4 * z) ^ (1 / 4 : ℝ) / Real.exp 1 := by
      linarith
    calc Real.log (4 * z) = 4 * Real.log ((4 * z) ^ (1 / 4 : ℝ)) := hlog_eq
      _ ≤ 4 * ((4 * z) ^ (1 / 4 : ℝ) / Real.exp 1) := by linarith
      _ = 4 * (4 * z) ^ (1 / 4 : ℝ) / Real.exp 1 := by ring
  have hlogpos : 0 ≤ Real.log (4 * z) := Real.log_nonneg (by linarith)
  have hsq : (Real.log (4 * z)) ^ 4 ≤ (4 * (4 * z) ^ (1 / 4 : ℝ) / Real.exp 1) ^ 4 :=
    pow_le_pow_left₀ hlogpos hlogb 4
  have hroot : ((4 * z) ^ (1 / 4 : ℝ)) ^ 4 = 4 * z := by
    rw [show (1 / 4 : ℝ) = ((4 : ℕ)⁻¹ : ℝ) by norm_num]
    exact Real.rpow_inv_natCast_pow ht.le (by norm_num)
  have hrhs : (4 * (4 * z) ^ (1 / 4 : ℝ) / Real.exp 1) ^ 4
      = 1024 * z / (Real.exp 1) ^ 4 := by
    rw [div_pow, mul_pow, hroot]
    ring
  have hone : (z + 1) * (Real.log (4 * z)) ^ 4 / z ^ 2
      ≤ (z + 1) * (1024 * z / (Real.exp 1) ^ 4) / z ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [← hrhs]
    exact mul_le_mul_of_nonneg_left hsq (by linarith)
  have he4 : (54.59 : ℝ) ≤ (Real.exp 1) ^ 4 := by
    calc (54.59 : ℝ) ≤ (2.7182818283 : ℝ) ^ 4 := by norm_num
      _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 4
  have heq : (z + 1) * (1024 * z / (Real.exp 1) ^ 4) / z ^ 2
      = (1024 / (Real.exp 1) ^ 4) * ((z + 1) / z) := by
    field_simp
  have hmid : (z + 1) * (1024 * z / (Real.exp 1) ^ 4) / z ^ 2
      ≤ (1024 / 54.59) * 1.025 := by
    rw [heq]
    have hf1 : (1024 : ℝ) / (Real.exp 1) ^ 4 ≤ 1024 / 54.59 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) he4
    have hz2 : (z + 1) / z ≤ 1.025 := by
      rw [div_le_iff₀ hz0]
      nlinarith [hz]
    exact mul_le_mul hf1 hz2 (by positivity) (by positivity)
  have hnum : (1024 / 54.59) * 1.025 ≤ (19.227 : ℝ) := by norm_num
  linarith [hone, hmid, hnum]

theorem solution (z : ℝ) (hz : 40 ≤ z) :
    (Real.log (4 * z)) ^ 2 / (2 * TaoFivePrimes.twinPrimeConstant) /
        (1 - ((z + 1) * ((Real.log (4 * z)) ^ 2 /
          (2 * TaoFivePrimes.twinPrimeConstant)) / (16 * z ^ 2)))
      ≤ ∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
        (if Squarefree q then
          ∏ p ∈ q.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
        else 0) / (1 + (q : ℝ) / z) := by
  have hz0 : 0 < z := by linarith
  obtain ⟨B₀, E₀, hE0, hE10, hB0, hB⟩ :=
    PrimePairSieve.reciprocal_base_denominator_quadratic_expansion_sharp
  obtain ⟨hClo, hChi, hγ, hP⟩ := PrimePairSieve.sieve_constants_certificate
  set S := (∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
    (if Squarefree q then
      ∏ p ∈ q.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
    else 0) / (1 + (q : ℝ) / z)) with hSdef
  set C := TaoFivePrimes.twinPrimeConstant with hCdef
  set L := Real.log z with hLdef
  set ℓ := Real.log (4 * z) with hℓdef
  set lam := Real.log 4 with hlamdef
  set s := (z + 1) * (ℓ ^ 2 / (2 * C)) / (16 * z ^ 2) with hsdef
  set α := 4 * Real.eulerMascheroniConstant +
    4 * (∑' p : Nat.Primes, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) -
    Real.log 2 with hαdef
  have hC0 : 0 < C := by linarith
  have hBz := hB z hz0
  rw [← hLdef] at hBz
  have hlog2 : Real.log 2 ≤ 0.6931471808 := Real.log_two_lt_d9.le
  have hαlo : (4.5556 : ℝ) ≤ α := by
    rw [hαdef]
    linarith [hγ, hP, hlog2]
  have hlamhi : lam ≤ 1.3862944 := by
    rw [hlamdef]
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [h4]
    linarith [Real.log_two_lt_d9.le]
  have hlam0 : 0 ≤ lam := by
    rw [hlamdef]
    exact Real.log_nonneg (by norm_num)
  have hlam2 : lam ^ 2 ≤ 1.9218122 := by nlinarith [hlamhi, hlam0]
  have hLlo : 3.6657359 ≤ L := by
    rw [hLdef]
    have h40 : Real.log 40 = Real.log 5 + 3 * Real.log 2 := by
      rw [show (40 : ℝ) = 5 * 2 ^ 3 by norm_num, Real.log_mul (by norm_num) (by positivity)]
      rw [Real.log_pow]
      push_cast
      ring
    have h5 : 1.6094379123 ≤ Real.log 5 := Real.log_five_gt_d9.le
    have h40' : 3.6657359 ≤ Real.log 40 := by rw [h40]; linarith [Real.log_two_gt_d9.le]
    exact h40'.trans (Real.log_le_log (by norm_num) hz)
  have hα2 : (1.7830112 : ℝ) ≤ α - 2 * lam := by linarith [hαlo, hlamhi]
  have hprod : 1.7830112 * 3.6657359 ≤ (α - 2 * lam) * L :=
    mul_le_mul hα2 hLlo (by norm_num) (by linarith)
  have hAvail : (4.6142 : ℝ) ≤ (α - 2 * lam) * L - lam ^ 2 := by nlinarith [hprod, hlam2]
  have hz13 : z ^ (-(1 / 3) : ℝ) ≤ 0.2925 := by
    have h40 : z ^ (-(1 / 3) : ℝ) ≤ (40 : ℝ) ^ (-(1 / 3) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hz (by norm_num)
    have h403 : (40 : ℝ) ^ (-(1 / 3) : ℝ) ≤ 0.2925 := by
      have hcube : ((40 : ℝ) ^ (-(1 / 3) : ℝ)) ^ 3 = (40 : ℝ)⁻¹ := by
        rw [← Real.rpow_natCast (x := (40 : ℝ) ^ (-(1 / 3))) (n := 3)]
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 40)]
        rw [show (-(1 / 3) : ℝ) * ((3 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
      have h0 : (0 : ℝ) ≤ (40 : ℝ) ^ (-(1 / 3) : ℝ) := Real.rpow_nonneg (by norm_num) _
      have h1 : ((40 : ℝ) ^ (-(1 / 3) : ℝ)) ^ 3 ≤ (0.2925 : ℝ) ^ 3 := by
        rw [hcube]
        norm_num
      exact (pow_le_pow_iff_left₀ h0 (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)).mp h1
    exact h40.trans h403
  have hw : 0 ≤ z ^ (-(1 / 3) : ℝ) := Real.rpow_nonneg hz0.le _
  have hCw : C * z ^ (-(1 / 3) : ℝ) ≤ 1.3217 * 0.2925 :=
    mul_le_mul hChi hz13 hw (by norm_num)
  have hK : (1.5 : ℝ) + (20 * C / 3) * z ^ (-(1 / 3) : ℝ) ≤ 4.07732 := by
    have h1 : (20 / 3 : ℝ) * (C * z ^ (-(1 / 3) : ℝ)) ≤
        (20 / 3) * (1.3217 * 0.2925) :=
      mul_le_mul_of_nonneg_left hCw (by norm_num)
    have h2 : (20 / 3 : ℝ) * (C * z ^ (-(1 / 3) : ℝ)) =
        (20 * C / 3) * z ^ (-(1 / 3) : ℝ) := by ring
    have h3 : (20 / 3 : ℝ) * (1.3217 * 0.2925) ≤ 2.57732 := by norm_num
    linarith
  have hs_eq : s = ((z + 1) * ℓ ^ 2 / z ^ 2) / (32 * C) := by
    rw [hsdef]
    field_simp
    ring
  have hf := sieve_f_bound z hz
  rw [← hℓdef] at hf
  have hs_le : s ≤ 0.01756 := by
    rw [hs_eq]
    have h1 : ((z + 1) * ℓ ^ 2 / z ^ 2) / (32 * C) ≤ 0.7024 / (32 * C) :=
      div_le_div_of_nonneg_right hf (by positivity)
    have h2 : (0.7024 : ℝ) / (32 * C) ≤ 0.7024 / 40 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith [hClo])
    have h3 : (0.7024 : ℝ) / 40 = 0.01756 := by norm_num
    linarith
  have h1ms : (0.98244 : ℝ) ≤ 1 - s := by linarith [hs_le]
  have hg := sieve_g_bound z hz
  rw [← hℓdef] at hg
  have hsℓ_eq : s * ℓ ^ 2 = ((z + 1) * ℓ ^ 4 / z ^ 2) / (32 * C) := by
    rw [hsdef]
    field_simp
    ring
  have hsℓ : s * ℓ ^ 2 ≤ 0.480675 := by
    rw [hsℓ_eq]
    have h1 : ((z + 1) * ℓ ^ 4 / z ^ 2) / (32 * C) ≤ 19.227 / (32 * C) :=
      div_le_div_of_nonneg_right hg (by positivity)
    have h2 : (19.227 : ℝ) / (32 * C) ≤ 19.227 / 40 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith [hClo])
    have h3 : (19.227 : ℝ) / 40 = 0.480675 := by norm_num
    linarith
  have hST : s * ℓ ^ 2 / (1 - s) ≤ 0.4893 := by
    have h := div_le_div₀ (by norm_num : (0 : ℝ) ≤ 0.480675) hsℓ
      (by norm_num : (0 : ℝ) < 0.98244) h1ms
    have hnum : (0.480675 : ℝ) / 0.98244 ≤ 0.4893 := by norm_num
    linarith
  have hℓL : ℓ = L + lam := by
    rw [hℓdef, hLdef, hlamdef]
    rw [Real.log_mul (by norm_num) (ne_of_gt hz0)]
    ring
  have hℓsq : ℓ ^ 2 = L ^ 2 + 2 * lam * L + lam ^ 2 := by
    rw [hℓL]
    ring
  have hST' : s * (L ^ 2 + 2 * lam * L + lam ^ 2) / (1 - s) ≤ 0.4893 := by
    rw [← hℓsq]
    exact hST
  have hsplit : ℓ ^ 2 / (1 - s) = ℓ ^ 2 + s * ℓ ^ 2 / (1 - s) := by
    field_simp
    ring
  have hred : ℓ ^ 2 / (1 - s) ≤
      L ^ 2 + α * L - 3 / 2 - (20 * C / 3) * z ^ (-(1 / 3) : ℝ) := by
    calc ℓ ^ 2 / (1 - s)
        = ℓ ^ 2 + s * ℓ ^ 2 / (1 - s) := hsplit
      _ ≤ (L ^ 2 + 2 * lam * L + lam ^ 2) + 0.4893 := by
          rw [hℓsq]
          linarith [hST']
      _ ≤ L ^ 2 + α * L - 3 / 2 - (20 * C / 3) * z ^ (-(1 / 3) : ℝ) := by
          nlinarith [hAvail, hK]
  clear hSdef hCdef hαdef hlamdef hℓdef hLdef hsdef hℓL hℓsq hsplit hST hST' hf hg
  have hlow : (L ^ 2 + α * L + B₀) / (2 * C) - E₀ * z ^ (-(1 / 3) : ℝ) ≤ S := by
    linarith [(abs_le.mp hBz).1]
  have hEw : E₀ * z ^ (-(1 / 3) : ℝ) ≤ (10 / 3) * z ^ (-(1 / 3) : ℝ) :=
    mul_le_mul_of_nonneg_right hE10 hw
  have hB0' : (L ^ 2 + α * L - 3 / 2) / (2 * C) ≤ (L ^ 2 + α * L + B₀) / (2 * C) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have hlow' : (L ^ 2 + α * L - 3 / 2) / (2 * C) - (10 / 3) * z ^ (-(1 / 3) : ℝ) ≤ S := by
    linarith
  have h2CB : L ^ 2 + α * L - 3 / 2 - (20 * C / 3) * z ^ (-(1 / 3) : ℝ) ≤ 2 * C * S := by
    have h2 := mul_le_mul_of_nonneg_left hlow' (by positivity : (0 : ℝ) ≤ 2 * C)
    have heq : 2 * C * ((L ^ 2 + α * L - 3 / 2) / (2 * C) - (10 / 3) * z ^ (-(1 / 3) : ℝ))
        = L ^ 2 + α * L - 3 / 2 - (20 * C / 3) * z ^ (-(1 / 3) : ℝ) := by
      rw [mul_sub, mul_div_cancel₀ _ (by positivity : (2 : ℝ) * C ≠ 0)]
      ring
    linarith [h2, heq]
  calc ℓ ^ 2 / (2 * C) / (1 - s)
      = ℓ ^ 2 / (1 - s) / (2 * C) := by ring
    _ ≤ (L ^ 2 + α * L - 3 / 2 - (20 * C / 3) * z ^ (-(1 / 3) : ℝ)) / (2 * C) :=
        div_le_div_of_nonneg_right hred (by positivity)
    _ ≤ S := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * C)]
        linarith [h2CB]
