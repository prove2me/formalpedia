-- Prove2me | solution 1 for TaoFivePrimes.prime_in_short_interval_of_finiteRH3290M
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T20:12:31.223662+00:00
-- url     : https://prove2.me/submissions/14b0b296-16d8-40f0-9972-b5ccfec7c41d

import Definitions.Def_DusartTable1ZeroRanges_433_20261018
import Definitions.Def_dusart_psi_433_20261014_ExplicitFormula
import Mathlib
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_LogarithmicZeroCount
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_PowerQuarterWeights
import Theorems.Thm_RamareSaouter2003_prime_interval_finite_range
import Theorems.Thm_TaoFivePrimes_positive_zero_nineteenth_moment_tail
import Theorems.Thm_TaoFivePrimes_prime_power_correction_nearby

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000


-- Inlined checked source: Solutions/ShortPrimeIntervalSmoothing.lean

/-!
# Integration estimates for the smoothed short-interval argument

These lemmas develop the analytic part of Ramaré--Saouter, Section 3. They
neither assume prime existence nor use either side of the circular platform
reduction. Finite RH is not asserted by this file.
-/

open MeasureTheory

namespace ShortPrimeIntervalSmoothing

theorem scaled_cpow_hasDerivAt (delta t : ℝ) (r : ℂ)
    (hbase : 0 < 1 + delta*t) (hr : r ≠ 0) :
    HasDerivAt (fun u : ℝ => ((1 + delta*u : ℝ) : ℂ)^r)
      ((delta : ℂ)*r*((1 + delta*t : ℝ) : ℂ)^(r-1)) t := by
  have hb : HasDerivAt (fun u : ℝ => 1 + delta*u) delta t := by
    convert (hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).const_mul delta) using 1 <;>
      first | rfl | simp only [zero_add, mul_one]
  have hh := (hasDerivAt_ofReal_cpow_const hbase.ne' hr).scomp t hb
  convert hh using 1 <;> first | rfl | simp only [Complex.real_smul]; ring

/-- A single integration-by-parts step; iteration yields the high-zero decay.
Both endpoint terms vanish by the stated weight conditions. -/
theorem integral_cpow_step (delta : ℝ) (hd : 0 < delta) (rho : ℂ)
    (hi : rho.im ≠ 0) (f f' : ℝ → ℂ) (_hf : Continuous f) (hf' : Continuous f')
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' t) t)
    (hzero : f 0 = 0) (hone : f 1 = 0) :
    (∫ t in (0 : ℝ)..1, f t * ((1 + delta*t : ℝ) : ℂ)^rho) =
      -(∫ t in (0 : ℝ)..1,
        f' t * (((1 + delta*t : ℝ) : ℂ)^(rho+1)/(rho+1)/(delta : ℂ))) := by
  let g : ℝ → ℂ := fun t => ((1 + delta*t : ℝ) : ℂ)^rho
  let G : ℝ → ℂ := fun t => ((1 + delta*t : ℝ) : ℂ)^(rho+1)/(rho+1)/(delta : ℂ)
  have hr : rho ≠ 0 := by intro h; apply hi; simp [h]
  have hr1 : rho+1 ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    apply hi
    simpa using him
  have hdc : (delta : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hpos (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 < 1 + delta*t := by
    nlinarith only [hd, ht.1]
  have hG (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : HasDerivAt G (g t) t := by
    have h := ((scaled_cpow_hasDerivAt delta t (rho+1) (hpos t ht) hr1).div_const
      (rho+1)).div_const (delta : ℂ)
    convert h using 1 <;> first | rfl |
      dsimp [G, g]; simp only [add_sub_cancel_right]; field_simp [hr1, hdc]
  have hg : ContinuousOn g (Set.uIcc (0 : ℝ) 1) := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa using ht
    exact (scaled_cpow_hasDerivAt delta t rho (hpos t ht') hr).continuousAt.continuousWithinAt
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t ht => hderiv t (by simpa using ht))
    (fun t ht => hG t (by simpa using ht))
    (hf'.intervalIntegrable 0 1) hg.intervalIntegrable
  simpa only [hzero, hone, zero_mul, sub_self, zero_sub] using hparts

/-- The Mellin moment after n integrations by parts. All differentiability and
endpoint hypotheses remain explicit; no numerical zero input is hidden here. -/
theorem integral_cpow_iterate (delta : ℝ) (hd : 0 < delta) (rho : ℂ)
    (hi : rho.im ≠ 0) (F : ℕ → ℝ → ℂ) (m : ℕ)
    (hc : ∀ k ≤ m, Continuous (F k))
    (hderiv : ∀ k < m, ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (F k) (F (k+1) t) t)
    (hz : ∀ k < m, F k 0 = 0) (ho : ∀ k < m, F k 1 = 0) :
    (∏ k ∈ Finset.range m, (rho + (k : ℂ) + 1)) * (delta : ℂ)^m *
      (∫ t in (0 : ℝ)..1, F 0 t * ((1+delta*t : ℝ) : ℂ)^rho) =
      (-1 : ℂ)^m * (∫ t in (0 : ℝ)..1, F m t *
        ((1+delta*t : ℝ) : ℂ)^(rho+(m : ℂ))) := by
  let J (k : ℕ) : ℂ := ∫ t in (0 : ℝ)..1,
    F k t * ((1+delta*t : ℝ) : ℂ)^(rho+(k : ℂ))
  have hstep (k : ℕ) (hk : k < m) :
      (delta : ℂ) * (rho+(k : ℂ)+1) * J k = -J (k+1) := by
    have hik : (rho+(k : ℂ)).im ≠ 0 := by simpa using hi
    have h := integral_cpow_step delta hd (rho+(k : ℂ)) hik (F k) (F (k+1))
      (hc k (Nat.le_of_lt hk)) (hc (k+1) hk) (hderiv k hk) (hz k hk) (ho k hk)
    simp_rw [← mul_div_assoc, intervalIntegral.integral_div] at h
    have hrk : rho+(k : ℂ)+1 ≠ 0 := by
      intro he
      apply hi
      have him := congrArg Complex.im he
      simpa using him
    have hdc : (delta : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hJ : (∫ t in (0 : ℝ)..1, F (k+1) t *
        ((1+delta*t : ℝ) : ℂ)^(rho+(k : ℂ)+1)) = J (k+1) := by
      dsimp [J]
      push_cast
      rw [add_assoc]
    change J k = -((∫ t in (0 : ℝ)..1, F (k+1) t *
      ((1+delta*t : ℝ) : ℂ)^(rho+(k : ℂ)+1)) / (rho+(k : ℂ)+1) / (delta : ℂ)) at h
    rw [hJ] at h
    rw [h]
    field_simp [hrk, hdc]
  have hiter : ∀ n ≤ m,
      (∏ k ∈ Finset.range n, (rho+(k : ℂ)+1)) * (delta : ℂ)^n * J 0 =
        (-1 : ℂ)^n * J n := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      have hn' : n < m := by omega
      have ih' := ih (Nat.le_of_lt hn')
      rw [Finset.prod_range_succ, pow_succ]
      calc
        _ = ((delta : ℂ)*(rho+(n : ℂ)+1)) *
            ((∏ k ∈ Finset.range n, (rho+(k : ℂ)+1)) * (delta : ℂ)^n * J 0) := by ring
        _ = ((delta : ℂ)*(rho+(n : ℂ)+1))*((-1 : ℂ)^n * J n) := by rw [ih']
        _ = (-1 : ℂ)^n * ((delta : ℂ)*(rho+(n : ℂ)+1)*J n) := by ring
        _ = (-1 : ℂ)^n * (-J (n+1)) := by rw [hstep n hn']
        _ = _ := by rw [pow_succ]; ring
  simpa [J] using hiter m le_rfl

theorem norm_cpow_on_unit_interval (delta : ℝ) (hd : 0 ≤ delta) (rho : ℂ)
    (hr0 : 0 ≤ rho.re) (hr1 : rho.re ≤ 1) (m : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖((1+delta*t : ℝ) : ℂ)^(rho+(m : ℂ))‖ ≤ (1+delta)^(m+1) := by
  have hp : 0 < 1+delta*t := by nlinarith [mul_nonneg hd ht.1]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hp]
  simp only [Complex.add_re, Complex.natCast_re]
  calc
    (1+delta*t)^(rho.re+(m : ℝ)) ≤ (1+delta)^(rho.re+(m : ℝ)) :=
      Real.rpow_le_rpow hp.le (by nlinarith [ht.2]) (by positivity)
    _ ≤ (1+delta)^((m+1 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
    _ = _ := Real.rpow_natCast _ _

theorem norm_moment_le_l1 (delta : ℝ) (hd : 0 ≤ delta) (rho : ℂ)
    (hr0 : 0 ≤ rho.re) (hr1 : rho.re ≤ 1) (m : ℕ)
    (f : ℝ → ℂ) (hf : Continuous f) :
    ‖∫ t in (0 : ℝ)..1, f t * ((1+delta*t : ℝ) : ℂ)^(rho+(m : ℂ))‖ ≤
      (1+delta)^(m+1) * (∫ t in (0 : ℝ)..1, ‖f t‖) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
  · exact Filter.Eventually.of_forall fun t ht => by
      rw [norm_mul, mul_comm ((1+delta)^(m+1))]
      exact mul_le_mul_of_nonneg_left
        (norm_cpow_on_unit_interval delta hd rho hr0 hr1 m t ⟨le_of_lt ht.1, ht.2⟩)
        (norm_nonneg _)
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

theorem norm_moment_decay (delta : ℝ) (hd : 0 < delta) (rho : ℂ)
    (hi : rho.im ≠ 0) (hr0 : 0 ≤ rho.re) (hr1 : rho.re ≤ 1)
    (F : ℕ → ℝ → ℂ) (m : ℕ)
    (hc : ∀ k ≤ m, Continuous (F k))
    (hderiv : ∀ k < m, ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (F k) (F (k+1) t) t)
    (hz : ∀ k < m, F k 0 = 0) (ho : ∀ k < m, F k 1 = 0) :
    ‖∫ t in (0 : ℝ)..1, F 0 t * ((1+delta*t : ℝ) : ℂ)^rho‖ ≤
      (1+delta)^(m+1) * (∫ t in (0 : ℝ)..1, ‖F m t‖) /
        (delta^m * |rho.im|^m) := by
  have hp : |rho.im|^m ≤ ‖∏ k ∈ Finset.range m, (rho+(k : ℂ)+1)‖ := by
    rw [norm_prod]
    calc
      |rho.im|^m = ∏ _k ∈ Finset.range m, |rho.im| := by simp
      _ ≤ ∏ k ∈ Finset.range m, ‖rho+(k : ℂ)+1‖ := by
        apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
        intro k _
        simpa using Complex.abs_im_le_norm (rho+(k : ℂ)+1)
  have h := congrArg norm (integral_cpow_iterate delta hd rho hi F m hc hderiv hz ho)
  simp only [norm_mul, norm_pow, Complex.norm_of_nonneg hd.le,
    norm_neg, norm_one, one_pow, one_mul] at h
  have hb := norm_moment_le_l1 delta hd.le rho hr0 hr1 m (F m) (hc m le_rfl)
  have hprod := mul_le_mul_of_nonneg_right hp
    (mul_nonneg (pow_nonneg hd.le m)
      (norm_nonneg (∫ t in (0 : ℝ)..1, F 0 t * ((1+delta*t : ℝ) : ℂ)^rho)))
  have hden : 0 < delta^m * |rho.im|^m := mul_pos (pow_pos hd m) (pow_pos (abs_pos.mpr hi) m)
  apply (le_div_iff₀ hden).mpr
  calc
    _ = |rho.im|^m * (delta^m *
      ‖∫ t in (0 : ℝ)..1, F 0 t * ((1+delta*t : ℝ) : ℂ)^rho‖) := by ring
    _ ≤ ‖∏ k ∈ Finset.range m, (rho+(k : ℂ)+1)‖ *
      (delta^m * ‖∫ t in (0 : ℝ)..1, F 0 t * ((1+delta*t : ℝ) : ℂ)^rho‖) := hprod
    _ = ‖∫ t in (0 : ℝ)..1, F m t * ((1+delta*t : ℝ) : ℂ)^(rho+(m : ℂ))‖ := by
      rw [← mul_assoc, h]
    _ ≤ _ := hb

end ShortPrimeIntervalSmoothing


-- Inlined checked source: Solutions/ShortPrimeIntervalWeight18.lean

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
# Exact polynomial integration for the short-interval smoothing weight

The source uses f(t) = (4*t*(1-t))^18 on [0,1]. Rational polynomial arithmetic
can certify its mass and derivative energy without numerical
quadrature. These are ingredients of the analytic proof, not an RH certificate.
-/

open MeasureTheory
open scoped BigOperators

namespace ShortPrimeIntervalWeight18

def qIntegral (N : ℕ) (c : ℕ → ℚ) (e : ℕ → ℕ) (a b : ℚ) : ℚ :=
  ∑ k ∈ Finset.range N,
    c k * ((b^(e k+1) - a^(e k+1)) / (e k+1 : ℚ))

theorem integral_eq_qIntegral (N : ℕ) (c : ℕ → ℚ) (e : ℕ → ℕ) (a b : ℚ) :
    (∫ t in (a : ℝ)..(b : ℝ), ∑ k ∈ Finset.range N, (c k : ℝ) * t^(e k)) =
      (qIntegral N c e a b : ℝ) := by
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul, integral_pow]
    unfold qIntegral
    push_cast
    rfl
  · intro k _
    exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- Explicit binomial coefficients, so the certificate evaluator is computable. -/
def weightCoeff (j : ℕ) : ℚ := 4^18 * (-1)^(18-j) * (Nat.choose 18 j : ℚ)

def weightExponent (j : ℕ) : ℕ := 18 + (18-j)

def weightIntegral (a b : ℚ) : ℚ := qIntegral 19 weightCoeff weightExponent a b

theorem weight_eq_sum (t : ℝ) :
    (4 * t * (1-t))^18 =
      ∑ j ∈ Finset.range 19, (weightCoeff j : ℝ) * t^(weightExponent j) := by
  rw [mul_pow, mul_pow, sub_eq_add_neg, add_pow]
  simp only [one_pow, one_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold weightCoeff weightExponent
  push_cast
  rw [neg_pow, pow_add]
  ring

theorem integral_weight (a b : ℚ) :
    (∫ t in (a : ℝ)..(b : ℝ), (4*t*(1-t))^18) = (weightIntegral a b : ℝ) := by
  simp_rw [weight_eq_sum]
  exact integral_eq_qIntegral _ _ _ _ _

theorem weight_mass_pos : 0 < weightIntegral 0 1 := by decide +kernel

theorem real_weight_mass_pos :
    0 < ∫ t in (0 : ℝ)..1, (4*t*(1-t))^18 := by
  have h := integral_weight 0 1
  norm_num only [Rat.cast_zero, Rat.cast_one] at h
  rw [h]
  exact_mod_cast weight_mass_pos

def derivativeCoeff (n j : ℕ) : ℚ :=
  weightCoeff j * (Nat.descFactorial (weightExponent j) n : ℚ)

def derivativeExponent (n j : ℕ) : ℕ := weightExponent j - n

theorem iteratedDeriv_weight (n : ℕ) (t : ℝ) :
    iteratedDeriv n (fun x : ℝ => (4*x*(1-x))^18) t =
      ∑ j ∈ Finset.range 19, (derivativeCoeff n j : ℝ)*t^(derivativeExponent n j) := by
  have heq : (fun x : ℝ => (4*x*(1-x))^18) =
      (fun x : ℝ => ∑ j ∈ Finset.range 19, (weightCoeff j : ℝ)*x^(weightExponent j)) :=
    funext weight_eq_sum
  rw [heq, iteratedDeriv_fun_sum]
  · simp [derivativeCoeff, derivativeExponent, mul_assoc]
  · intro j _
    fun_prop

theorem derivative_at_one_certificate :
    ∀ n ∈ Finset.range 18, (∑ j ∈ Finset.range 19, derivativeCoeff n j) = 0 := by
  decide +kernel

theorem lower_endpoint_vanishing (n : ℕ) (hn : n < 18) :
    iteratedDeriv n (fun x : ℝ => (4*x*(1-x))^18) 0 = 0 := by
  rw [iteratedDeriv_weight]
  apply Finset.sum_eq_zero
  intro j _
  have hpos : 0 < derivativeExponent n j := by
    unfold derivativeExponent weightExponent
    omega
  simp [zero_pow hpos.ne']

theorem upper_endpoint_vanishing (n : ℕ) (hn : n < 18) :
    iteratedDeriv n (fun x : ℝ => (4*x*(1-x))^18) 1 = 0 := by
  rw [iteratedDeriv_weight]
  simp only [one_pow, mul_one]
  exact_mod_cast derivative_at_one_certificate n (Finset.mem_range.mpr hn)

def qEnergy (N : ℕ) (c : ℕ → ℚ) (e : ℕ → ℕ) (a b : ℚ) : ℚ :=
  ∑ i ∈ Finset.range N, qIntegral N (fun j => c i*c j) (fun j => e i+e j) a b

theorem integral_square_eq_qEnergy (N : ℕ) (c : ℕ → ℚ) (e : ℕ → ℕ) (a b : ℚ) :
    (∫ t in (a : ℝ)..(b : ℝ), (∑ j ∈ Finset.range N, (c j : ℝ)*t^(e j))^2) =
      (qEnergy N c e a b : ℝ) := by
  have heq (t : ℝ) : (∑ j ∈ Finset.range N, (c j : ℝ)*t^(e j))^2 =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        ((c i*c j : ℚ) : ℝ)*t^(e i+e j) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    rw [pow_add]
    ring
  simp_rw [heq]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [integral_eq_qIntegral]
    exact_mod_cast (rfl : (∑ i ∈ Finset.range N,
      qIntegral N (fun j => c i*c j) (fun j => e i+e j) a b) = qEnergy N c e a b)
  · intro i _
    exact Continuous.intervalIntegrable (by fun_prop) _ _

theorem weight_mass_exact :
    weightIntegral 0 1 = (4 : ℚ)^18 * (Nat.factorial 18 : ℚ)^2 / Nat.factorial 37 := by
  decide +kernel

theorem derivative_energy_exact :
    qEnergy 19 (derivativeCoeff 18) (derivativeExponent 18) 0 1 =
      (4 : ℚ)^36 * (Nat.factorial 18 : ℚ)^2 / 37 := by
  decide +kernel

theorem real_derivative_energy :
    (∫ t in (0 : ℝ)..1, (iteratedDeriv 18 (fun x : ℝ => (4*x*(1-x))^18) t)^2) =
      (((4 : ℚ)^36 * (Nat.factorial 18 : ℚ)^2 / 37 : ℚ) : ℝ) := by
  simp_rw [iteratedDeriv_weight]
  have h := integral_square_eq_qEnergy 19 (derivativeCoeff 18) (derivativeExponent 18) 0 1
  simp only [Rat.cast_zero, Rat.cast_one] at h
  rw [h, derivative_energy_exact]

theorem integral_abs_sq_le (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ t in (0 : ℝ)..1, |g t|)^2 ≤ ∫ t in (0 : ℝ)..1, (g t)^2 := by
  let I : ℝ := ∫ t in (0 : ℝ)..1, |g t|
  have hnon : 0 ≤ ∫ t in (0 : ℝ)..1, (|g t|-I)^2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => sq_nonneg _)
  have heq : (fun t : ℝ => (|g t|-I)^2) =
      (fun t : ℝ => (g t)^2 - (2*I)*|g t| + I^2) := by
    funext t
    nlinarith [sq_abs (g t)]
  rw [heq, intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul] at hnon
  · simp only [intervalIntegral.integral_const, sub_zero, one_smul] at hnon
    dsimp [I] at hnon
    nlinarith
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

def derivativeRatio : ℚ := (Nat.factorial 37 : ℚ) / (Nat.factorial 18 * 6)

theorem derivativeRatio_pos : 0 < derivativeRatio := by decide +kernel

theorem derivative_energy_bound :
    (4 : ℚ)^36 * (Nat.factorial 18 : ℚ)^2 / 37 ≤
      (weightIntegral 0 1)^2 * derivativeRatio^2 := by
  rw [weight_mass_exact]
  decide +kernel

theorem weight_contDiff : ContDiff ℝ ⊤ (fun t : ℝ => (4*t*(1-t))^18) := by
  fun_prop

theorem derivative_l1_of_energy (n : ℕ) (cap : ℚ) (hcap : 0 ≤ cap)
    (he : qEnergy 19 (derivativeCoeff n) (derivativeExponent n) 0 1 ≤
      (weightIntegral 0 1)^2 * cap^2) :
    (∫ t in (0 : ℝ)..1, |iteratedDeriv n (fun x : ℝ => (4*x*(1-x))^18) t|) ≤
      (∫ t in (0 : ℝ)..1, (4*t*(1-t))^18) * (cap : ℝ) := by
  have hd : Continuous (iteratedDeriv n (fun x : ℝ => (4*x*(1-x))^18)) := by
    rw [show iteratedDeriv n (fun x : ℝ => (4*x*(1-x))^18) =
      (fun t : ℝ => ∑ j ∈ Finset.range 19,
        (derivativeCoeff n j : ℝ)*t^(derivativeExponent n j)) from funext (iteratedDeriv_weight n)]
    fun_prop
  have hsq := integral_abs_sq_le _ hd
  have henergy : (∫ t in (0 : ℝ)..1,
      (iteratedDeriv n (fun x : ℝ => (4*x*(1-x))^18) t)^2) =
      (qEnergy 19 (derivativeCoeff n) (derivativeExponent n) 0 1 : ℝ) := by
    simp_rw [iteratedDeriv_weight]
    have h := integral_square_eq_qEnergy 19 (derivativeCoeff n) (derivativeExponent n) 0 1
    simpa only [Rat.cast_zero, Rat.cast_one] using h
  rw [henergy] at hsq
  have he' : (qEnergy 19 (derivativeCoeff n) (derivativeExponent n) 0 1 : ℝ) ≤
      (weightIntegral 0 1 : ℝ)^2 * (cap : ℝ)^2 := by exact_mod_cast he
  have hm := real_weight_mass_pos
  have hk : 0 ≤ (cap : ℝ) := by exact_mod_cast hcap
  have hw := integral_weight 0 1
  simp only [Rat.cast_zero, Rat.cast_one] at hw
  rw [hw] at hm ⊢
  nlinarith [mul_nonneg hm.le hk]

theorem derivative_l1_bound :
    (∫ t in (0 : ℝ)..1, |iteratedDeriv 18 (fun x : ℝ => (4*x*(1-x))^18) t|) ≤
      (∫ t in (0 : ℝ)..1, (4*t*(1-t))^18) * (derivativeRatio : ℝ) := by
  apply derivative_l1_of_energy 18 derivativeRatio derivativeRatio_pos.le
  rw [derivative_energy_exact]
  exact derivative_energy_bound

theorem second_derivative_energy_bound :
    qEnergy 19 (derivativeCoeff 2) (derivativeExponent 2) 0 1 ≤
      (weightIntegral 0 1)^2 * 256^2 := by decide +kernel

theorem second_derivative_l1_bound :
    (∫ t in (0 : ℝ)..1, |iteratedDeriv 2 (fun x : ℝ => (4*x*(1-x))^18) t|) ≤
      (∫ t in (0 : ℝ)..1, (4*t*(1-t))^18) * 256 := by
  exact_mod_cast derivative_l1_of_energy 2 256 (by norm_num) second_derivative_energy_bound

end ShortPrimeIntervalWeight18


-- Inlined checked source: Solutions/ShortPrimeIntervalMellin18.lean

noncomputable section
open MeasureTheory

namespace ShortPrimeIntervalMellin18

def f (t : ℝ) : ℝ := (4*t*(1-t))^18

def F (n : ℕ) (t : ℝ) : ℂ := (iteratedDeriv n f t : ℝ)

def mass : ℝ := ∫ t in (0 : ℝ)..1, f t

def mu : ℝ := (ShortPrimeIntervalWeight18.derivativeRatio : ℝ)

theorem mass_pos : 0 < mass := ShortPrimeIntervalWeight18.real_weight_mass_pos

theorem F_continuous (n : ℕ) : Continuous (F n) := by
  have h := ContDiff.continuous_iteratedDeriv n ShortPrimeIntervalWeight18.weight_contDiff (by simp)
  exact Complex.continuous_ofReal.comp h

theorem F_hasDerivAt (n : ℕ) (t : ℝ) : HasDerivAt (F n) (F (n+1) t) t := by
  have h := ContDiff.differentiable_iteratedDeriv n ShortPrimeIntervalWeight18.weight_contDiff (by simp)
  have hd := (h t).hasDerivAt.ofReal_comp
  dsimp only [F]
  rw [iteratedDeriv_succ]
  convert hd using 1 <;> rfl

theorem F_zero (n : ℕ) (hn : n < 18) : F n 0 = 0 := by
  unfold F f
  rw [ShortPrimeIntervalWeight18.lower_endpoint_vanishing n hn]
  norm_num

theorem F_one (n : ℕ) (hn : n < 18) : F n 1 = 0 := by
  unfold F f
  rw [ShortPrimeIntervalWeight18.upper_endpoint_vanishing n hn]
  norm_num

theorem F_l1 : (∫ t in (0 : ℝ)..1, ‖F 18 t‖) ≤ mass*mu := by
  have h := ShortPrimeIntervalWeight18.derivative_l1_bound
  convert h using 1 <;> first | rfl |
    (simp only [F, Complex.norm_real, Real.norm_eq_abs] <;> rfl)

theorem F2_l1 : (∫ t in (0 : ℝ)..1, ‖F 2 t‖) ≤ mass*256 := by
  have h := ShortPrimeIntervalWeight18.second_derivative_l1_bound
  convert h using 1 <;> first | rfl |
    (simp only [F, Complex.norm_real, Real.norm_eq_abs] <;> rfl)

/-- The concrete, normalized order-18 Mellin decay used by the unsieved
interval calculation. All weight hypotheses have been discharged. -/
theorem normalized_mellin_decay (delta : ℝ) (hd : 0 < delta) (rho : ℂ)
    (hi : rho.im ≠ 0) (hr0 : 0 ≤ rho.re) (hr1 : rho.re ≤ 1) :
    ‖(∫ t in (0 : ℝ)..1, (f t : ℂ)*((1+delta*t : ℝ) : ℂ)^rho)/(mass : ℂ)‖ ≤
      (1+delta)^19*mu/(delta^18*|rho.im|^18) := by
  have h := ShortPrimeIntervalSmoothing.norm_moment_decay delta hd rho hi hr0 hr1 F 18
    (fun n _ => F_continuous n) (fun n _ t _ => F_hasDerivAt n t) F_zero F_one
  simp only [F, iteratedDeriv_zero] at h
  have hl := F_l1
  have hb : ‖∫ t in (0 : ℝ)..1, (f t : ℂ)*((1+delta*t : ℝ) : ℂ)^rho‖ ≤
      (1+delta)^19*(mass*mu)/(delta^18*|rho.im|^18) := by
    apply h.trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hl (by positivity)) (by positivity)
  rw [norm_div, Complex.norm_of_nonneg mass_pos.le]
  apply (div_le_iff₀ mass_pos).mpr
  exact hb.trans_eq (by ring)

/-- A uniform remainder estimate pairs with the checked second-derivative
L1 bound. No continuity or measurability is hidden in this norm inequality. -/
theorem weighted_remainder_bound (R : ℝ → ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hR : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖R t‖ ≤ K) :
    ‖∫ t in (0 : ℝ)..1, F 2 t * R t‖ ≤ K*(mass*256) := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le
    (a := (0 : ℝ)) (b := 1) (f := fun t => F 2 t * R t) (by norm_num)
    (g := fun t => K*‖F 2 t‖)
    (Filter.Eventually.of_forall fun t ht => by
      rw [norm_mul]
      simpa only [mul_comm K] using mul_le_mul_of_nonneg_left
        (hR t ⟨ht.1.le, ht.2⟩) (norm_nonneg (F 2 t)))
    (((F_continuous 2).norm.const_mul K).intervalIntegrable (μ := volume) 0 1)
  rw [intervalIntegral.integral_const_mul] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left F2_l1 hK)

end ShortPrimeIntervalMellin18


-- Inlined checked source: Solutions/ShortPrimeIntervalKernelMellin18.lean

noncomputable section
open MeasureTheory
namespace ShortPrimeIntervalKernelMellin18
open DusartSmoothing
open ShortPrimeIntervalMellin18 (f F mass mass_pos)

def moment (delta : ℝ) (rho : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (f t : ℂ)*((1+delta*t : ℝ) : ℂ)^rho

theorem quadratic_kernel_mellin (X delta : ℝ) (hX : 0 < X) (hd : 0 < delta)
    (rho : ℂ) (hr : 0 < rho.re) (hi : rho.im ≠ 0) :
    (∫ t in (0 : ℝ)..1, F 2 t*quadraticKernel (X+X*delta*t) rho)/((X*delta : ℝ) : ℂ)^2 =
      (X : ℂ)^rho/rho * moment delta rho := by
  have hIBP := ShortPrimeIntervalSmoothing.integral_cpow_iterate delta hd rho hi F 2
    (fun n _ => ShortPrimeIntervalMellin18.F_continuous n)
    (fun n _ t _ => ShortPrimeIntervalMellin18.F_hasDerivAt n t)
    (fun n hn => ShortPrimeIntervalMellin18.F_zero n (by omega))
    (fun n hn => ShortPrimeIntervalMellin18.F_one n (by omega))
  have hprod : (∏ k ∈ Finset.range 2, (rho+(k : ℂ)+1)) = (rho+1)*(rho+2) := by
    norm_num [Finset.prod_range_succ, add_assoc]
  have hf0 : F 0 = (fun t => (f t : ℂ)) := by
    funext t
    simp only [F, iteratedDeriv_zero]
  rw [hprod, hf0] at hIBP
  simp only [neg_one_sq, one_mul, Nat.cast_ofNat] at hIBP
  change (rho+1)*(rho+2)*(delta : ℂ)^2*moment delta rho =
    ∫ t in (0 : ℝ)..1, F 2 t*((1+delta*t : ℝ) : ℂ)^(rho+2) at hIBP
  have hker (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      quadraticKernel (X+X*delta*t) rho =
        ((X : ℂ)^(rho+2)/(rho*(rho+1)*(rho+2)))*((1+delta*t : ℝ) : ℂ)^(rho+2) := by
    have hbase : 0 ≤ 1+delta*t := by nlinarith [ht.1]
    unfold quadraticKernel
    rw [show X+X*delta*t = X*(1+delta*t) by ring, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg hX.le hbase]
    ring
  have hInt : (∫ t in (0 : ℝ)..1, F 2 t*quadraticKernel (X+X*delta*t) rho) =
      ((X : ℂ)^(rho+2)/(rho*(rho+1)*(rho+2))) *
        (∫ t in (0 : ℝ)..1, F 2 t*((1+delta*t : ℝ) : ℂ)^(rho+2)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [hker t (by simpa using ht)]
    ring
  have hXc : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hdc : (delta : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  have hr0 : rho ≠ 0 := by intro h; simp [h] at hr
  have hr1 : rho+1 ≠ 0 := by intro h; have hh := congrArg Complex.re h; simp at hh; linarith
  have hr2 : rho+2 ≠ 0 := by intro h; have hh := congrArg Complex.re h; simp at hh; linarith
  rw [hInt, ← hIBP, Complex.cpow_add rho 2 hXc, Complex.cpow_two, Complex.ofReal_mul]
  field_simp [hXc, hdc, hr0, hr1, hr2]
  <;> ring

theorem norm_exp_quotient_low (u : ℝ) (hu : 0 ≤ u) (rho : ℂ) (hr : rho ≠ 0)
    (hbeta : 0 ≤ rho.re) :
    ‖(Complex.exp (rho*(u : ℂ))-1)/rho‖ ≤ u*Real.exp (u*rho.re) := by
  have hInt := integral_exp_mul_complex (a := (0 : ℝ)) (b := u) hr
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at hInt
  rw [← hInt]
  have hb : ∀ t ∈ Set.uIoc (0 : ℝ) u, ‖Complex.exp (rho*(t : ℂ))‖ ≤ Real.exp (u*rho.re) := by
    intro t ht
    rw [Set.uIoc_of_le hu] at ht
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact Real.exp_le_exp.mpr (by nlinarith [ht.2])
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa only [sub_zero, abs_of_nonneg hu, mul_comm] using h

theorem norm_normalized_moment_low (delta : ℝ) (hd : 0 ≤ delta) (rho : ℂ)
    (hr : rho.re = 1/2) :
    ‖moment delta rho/(mass : ℂ)‖ ≤ Real.sqrt (1+delta) := by
  have hnon (t : ℝ) : 0 ≤ f t := by unfold f; positivity
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(f t : ℂ)*((1+delta*t : ℝ) : ℂ)^rho‖ ≤ Real.sqrt (1+delta)*f t := by
    intro t ht
    have hp : 0 < 1+delta*t := by nlinarith [mul_nonneg hd ht.1]
    rw [norm_mul, Complex.norm_of_nonneg (hnon t), Complex.norm_cpow_eq_rpow_re_of_pos hp, hr]
    have hb : (1+delta*t)^(1/2 : ℝ) ≤ Real.sqrt (1+delta) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow hp.le (by nlinarith [ht.2]) (by norm_num)
    nlinarith only [mul_le_mul_of_nonneg_left hb (hnon t)]
  have h := intervalIntegral.norm_integral_le_of_norm_le
    (a := (0 : ℝ)) (b := 1) (by norm_num)
    (Filter.Eventually.of_forall fun t ht => hbound t ⟨ht.1.le, ht.2⟩)
    (Continuous.intervalIntegrable (μ := volume) (by unfold f; fun_prop) _ _)
  rw [intervalIntegral.integral_const_mul] at h
  rw [norm_div, Complex.norm_of_nonneg mass_pos.le]
  apply (div_le_iff₀ mass_pos).mpr
  exact h

end ShortPrimeIntervalKernelMellin18


-- Inlined checked source: Solutions/ShortPrimeIntervalIncrement18.lean

noncomputable section
namespace ShortPrimeIntervalIncrement18
open ShortPrimeIntervalMellin18 (mass mu)
open ShortPrimeIntervalKernelMellin18 (moment)

def kernel (X u delta : ℝ) (rho : ℂ) : ℂ :=
  (X : ℂ)^rho * ((Complex.exp (rho*(u : ℂ))-1)/rho) *
    (moment delta rho/(mass : ℂ))

theorem norm_kernel_low (X u delta : ℝ) (hX : 0 < X) (hu : 0 ≤ u)
    (hd : 0 ≤ delta) (rho : ℂ) (hr : rho.re = 1/2) :
    ‖kernel X u delta rho‖ ≤
      u*Real.sqrt X*Real.exp (u/2)*Real.sqrt (1+delta) := by
  have hn : rho ≠ 0 := by intro h; simp [h] at hr
  have hq := ShortPrimeIntervalKernelMellin18.norm_exp_quotient_low u hu rho hn
    (by rw [hr]; norm_num)
  have hm := ShortPrimeIntervalKernelMellin18.norm_normalized_moment_low delta hd rho hr
  have hb : ‖(X : ℂ)^rho‖ = Real.sqrt X := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX, hr, Real.sqrt_eq_rpow]
  rw [kernel, norm_mul, norm_mul, hb]
  calc
    _ ≤ Real.sqrt X*(u*Real.exp (u*rho.re))*Real.sqrt (1+delta) := by gcongr
    _ = _ := by
      rw [hr, show u*(1/2 : ℝ) = u/2 by ring]
      ring

theorem norm_exp_quotient_high (u : ℝ) (hu : 0 ≤ u) (rho : ℂ)
    (hi : rho.im ≠ 0) (hr : rho.re ≤ 1) :
    ‖(Complex.exp (rho*(u : ℂ))-1)/rho‖ ≤
      (Real.exp u+1)/|rho.im| := by
  have him : 0 < |rho.im| := abs_pos.mpr hi
  have hn : 0 < ‖rho‖ := him.trans_le (Complex.abs_im_le_norm rho)
  have he : ‖Complex.exp (rho*(u : ℂ))‖ ≤ Real.exp u := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith
  rw [norm_div]
  calc
    _ ≤ (Real.exp u+1)/‖rho‖ := by
      apply div_le_div_of_nonneg_right _ hn.le
      exact (norm_sub_le _ _).trans (by simpa using add_le_add_right he 1)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) him (Complex.abs_im_le_norm rho)

theorem norm_kernel_high (X u delta : ℝ) (hX : 0 < X) (hu : 0 ≤ u)
    (hd : 0 < delta) (rho : ℂ) (hi : rho.im ≠ 0)
    (hr0 : 0 ≤ rho.re) (hr1 : rho.re ≤ 1) :
    ‖kernel X u delta rho‖ ≤
      ((Real.exp u+1)*(1+delta)^19*mu*X/delta^18)*
        (X^(rho.re-1)*(1/|rho.im|^19)) := by
  have hq := norm_exp_quotient_high u hu rho hi hr1
  have hm := ShortPrimeIntervalMellin18.normalized_mellin_decay delta hd rho hi hr0 hr1
  change ‖moment delta rho/(mass : ℂ)‖ ≤ _ at hm
  have hxpow : X^rho.re = X*X^(rho.re-1) := by
    rw [Real.rpow_sub hX, Real.rpow_one]
    field_simp
  rw [kernel, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX]
  calc
    _ ≤ X^rho.re*((Real.exp u+1)/|rho.im|)*
        ((1+delta)^19*mu/(delta^18*|rho.im|^18)) := by gcongr
    _ = _ := by
      rw [hxpow]
      field_simp
      <;> ring

theorem cpow_exp_scale (X u : ℝ) (hX : 0 < X) (rho : ℂ) :
    ((X*Real.exp u : ℝ) : ℂ)^rho =
      (X : ℂ)^rho*Complex.exp (rho*(u : ℂ)) := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hX.le (Real.exp_pos u).le]
  congr 1
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos u).ne'),
    ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
  congr 1
  ring

theorem kernel_difference (X u delta : ℝ) (hX : 0 < X) (rho : ℂ) :
    (((X*Real.exp u : ℝ) : ℂ)^rho/rho)*(moment delta rho/(mass : ℂ)) -
      ((X : ℂ)^rho/rho)*(moment delta rho/(mass : ℂ)) = kernel X u delta rho := by
  rw [cpow_exp_scale X u hX]
  unfold kernel
  ring

end ShortPrimeIntervalIncrement18


-- Inlined checked source: Solutions/ShortPrimeIntervalLowZeros18.lean

noncomputable section
open DusartSmoothing
namespace ShortPrimeIntervalLowZeros18

theorem finite_positive_count (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (T : ℝ) (hT : (10 : ℝ)^8 ≤ T) (hγ : ∀ ρ ∈ Z, ρ.im ≤ T) :
    (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ)) ≤ (17/100 : ℝ)*T*Real.log T := by
  have h1 := finite_actual_zero_count_bound Z hZ T (by norm_num at hT ⊢; linarith)
  have h2 := ExplicitPNT.DusartTable1.Modules.LogarithmicZeroCount.1 T (17/100)
    (by norm_num at hT ⊢; linarith) (by norm_num at hT ⊢; linarith)
  have he : finiteZeroCount Z RvM.zeroMult Complex.im T = ∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    simp only [primeStep, if_pos (hγ ρ hρ), mul_one]
  rw [he] at h1
  exact h1.trans h2

theorem finite_absolute_count (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ)
    (T : ℝ) (hT : (10 : ℝ)^8 ≤ T) (hγ : ∀ ρ ∈ Z, |ρ.im| ≤ T) :
    (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ)) ≤ 2*((17/100 : ℝ)*T*Real.log T) := by
  classical
  let W : ℝ → ℝ := fun t => if t ≤ T then 1 else 0
  have hp (S : Finset ℂ)
      (hS : ∀ ρ ∈ S, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im) :
      (∑ ρ ∈ S, (RvM.zeroMult ρ : ℝ)*W ρ.im) ≤ (17/100 : ℝ)*T*Real.log T := by
    let F := S.filter (fun ρ => ρ.im ≤ T)
    have h := finite_positive_count F
      (fun ρ hρ => hS ρ (Finset.mem_filter.mp hρ).1) T hT
      (fun ρ hρ => (Finset.mem_filter.mp hρ).2)
    simpa only [F, W, Finset.sum_filter, mul_ite, mul_one, mul_zero] using h
  have h := ExplicitPNT.DusartTable1.Modules.PowerQuarterWeights.1 W
    ((17/100 : ℝ)*T*Real.log T) hp Z hZ
  have he : (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ)*W |ρ.im|) = ∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    simp only [W, if_pos (hγ ρ hρ), mul_one]
  rw [he] at h
  exact h

def lowZeros (T : ℝ) : Finset NontrivialZetaZero :=
  ((RvM.finite_symmetric_zero_window T).preimage Subtype.val_injective.injOn).toFinset

theorem mem_lowZeros (T : ℝ) (ρ : NontrivialZetaZero) :
    ρ ∈ lowZeros T ↔ |ρ.val.im| ≤ T := by
  simp [lowZeros, ρ.property]

theorem total_low_count (T : ℝ) (hT : (10 : ℝ)^8 ≤ T) :
    (∑ ρ ∈ lowZeros T, (RvM.zeroMult ρ.val : ℝ)) ≤
      2*((17/100 : ℝ)*T*Real.log T) := by
  classical
  let Z := (lowZeros T).image (fun ρ : NontrivialZetaZero => ρ.val)
  have hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ := by
    intro ρ hρ
    obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp hρ
    exact τ.property
  have hγ : ∀ ρ ∈ Z, |ρ.im| ≤ T := by
    intro ρ hρ
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hρ
    exact (mem_lowZeros T τ).mp hτ
  have h := finite_absolute_count Z hZ T hT hγ
  dsimp [Z] at h
  rw [Finset.sum_image (fun a _ b _ he => Subtype.val_injective he)] at h
  exact h

theorem log_fixed_T_le : Real.log (1100000000 : ℝ) ≤ 21 := by
  have he : (27/10 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27/10) he 21
  rw [← Real.exp_nat_mul] at h
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 1100000000)).mpr
  exact (show (1100000000 : ℝ) ≤ (27/10 : ℝ)^21 by norm_num).trans (by simpa only [Nat.cast_ofNat, mul_one] using h)

theorem total_low_count_fixed :
    (∑ ρ ∈ lowZeros 1100000000, (RvM.zeroMult ρ.val : ℝ)) ≤ (7854000000 : ℝ) := by
  have h := total_low_count 1100000000 (by norm_num)
  nlinarith only [h, log_fixed_T_le]

end ShortPrimeIntervalLowZeros18


-- Inlined checked source: Solutions/ShortPrimeIntervalZeroMoments.lean

set_option maxHeartbeats 1000000
noncomputable section
open ExplicitPNT.DusartTable1
namespace ShortPrimeIntervalZeroMoments

/-- The actual positive-zero estimate gives both signs of the imaginary part. -/
theorem finite_absolute_tail (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ)
    (H : ℝ) (hH : (10 : ℝ)^8 ≤ H) (hlog : Real.log H ≤ 22)
    (hγ : ∀ ρ ∈ Z, H < |ρ.im|) :
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ)*(1/|ρ.im|^19)) ≤ 1/(2*H^18) := by
  classical
  let W : ℝ → ℝ := fun t => if H < t then 1/t^19 else 0
  have hpos (S : Finset ℂ)
      (hS : ∀ ρ ∈ S, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im) :
      (∑ ρ ∈ S, (DusartSmoothing.RvM.zeroMult ρ : ℝ)*W ρ.im) ≤ 1/(4*H^18) := by
    let F := S.filter (fun ρ => H < ρ.im)
    have hF : ∀ ρ ∈ F, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im :=
      fun ρ hρ => hS ρ (Finset.mem_filter.mp hρ).1
    have h := TaoFivePrimes.positive_zero_nineteenth_moment_tail F hF H hH hlog
      (fun ρ hρ => (Finset.mem_filter.mp hρ).2)
    simpa only [F, W, Finset.sum_filter, mul_ite, mul_zero] using h
  have h := ExplicitPNT.DusartTable1.Modules.PowerQuarterWeights.1 W (1/(4*H^18)) hpos Z hZ
  have he : (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ)*W |ρ.im|) =
      ∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ)*(1/|ρ.im|^19) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    simp only [W, if_pos (hγ ρ hρ)]
  rw [he] at h
  exact h.trans_eq (by ring)

theorem absolute_tail (H : ℝ) (hH : (10 : ℝ)^8 ≤ H) (hlog : Real.log H ≤ 22) :
    (∑' ρ : StrictHighAbsoluteZero H,
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ)*(1/|ρ.val.im|^19)) ≤ 1/(2*H^18) := by
  classical
  apply Real.tsum_le_of_sum_le
  · intro ρ
    positivity
  · intro S
    let Z : Finset ℂ := S.image (fun ρ : StrictHighAbsoluteZero H => ρ.val)
    have hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ := by
      intro ρ hρ
      obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp hρ
      exact τ.property.1
    have hγ : ∀ ρ ∈ Z, H < |ρ.im| := by
      intro ρ hρ
      obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp hρ
      exact τ.property.2
    have h := finite_absolute_tail Z hZ H hH hlog hγ
    dsimp [Z] at h
    rw [Finset.sum_image (fun a _ b _ he => Subtype.val_injective he)] at h
    exact h

/-- Finite RH is kept as a hypothesis: below H the weight is x^(-1/2),
and above H the unconditional absolute moment suffices. -/
theorem finite_weighted_tail_of_finite_rh (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ)
    (x T H : ℝ) (hx : 1 ≤ x) (hT : (10 : ℝ)^8 ≤ T) (hTH : T ≤ H)
    (hlog : Real.log H ≤ 22) (hγ : ∀ ρ ∈ Z, T < |ρ.im|)
    (hRH : ∀ ρ : ℂ, DusartSmoothing.RvM.IsNontrivialZero ρ → |ρ.im| ≤ H → ρ.re = 1/2) :
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ)*
      x^(ρ.re-1)*(1/|ρ.im|^19)) ≤ 1/(2*Real.sqrt x*T^18)+1/(2*H^18) := by
  classical
  let Zlo := Z.filter (fun ρ => |ρ.im| ≤ H)
  let Zhi := Z.filter (fun ρ => ¬|ρ.im| ≤ H)
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hT0 : 0 < T := by norm_num at hT; linarith
  have hTlog : Real.log T ≤ 22 := (Real.log_le_log hT0 hTH).trans hlog
  have hlow := finite_absolute_tail Zlo
    (fun ρ hρ => hZ ρ (Finset.mem_filter.mp hρ).1) T hT hTlog
    (fun ρ hρ => hγ ρ (Finset.mem_filter.mp hρ).1)
  have hhigh := finite_absolute_tail Zhi
    (fun ρ hρ => hZ ρ (Finset.mem_filter.mp hρ).1) H (hT.trans hTH) hlog
    (fun ρ hρ => lt_of_not_ge (Finset.mem_filter.mp hρ).2)
  have hsqrt : x^((1/2 : ℝ)-1) = 1/Real.sqrt x := by
    rw [show (1/2 : ℝ)-1 = -(1/2 : ℝ) by ring, Real.rpow_neg hx0.le,
      ← Real.sqrt_eq_rpow, one_div]
  have hl : (∑ ρ ∈ Zlo, (DusartSmoothing.RvM.zeroMult ρ : ℝ)*
      x^(ρ.re-1)*(1/|ρ.im|^19)) ≤ 1/(2*Real.sqrt x*T^18) := by
    have he : (∑ ρ ∈ Zlo, (DusartSmoothing.RvM.zeroMult ρ : ℝ)*
        x^(ρ.re-1)*(1/|ρ.im|^19)) =
        (1/Real.sqrt x)*(∑ ρ ∈ Zlo, (DusartSmoothing.RvM.zeroMult ρ : ℝ)*(1/|ρ.im|^19)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ hρ
      rw [hRH ρ (hZ ρ (Finset.mem_filter.mp hρ).1) (Finset.mem_filter.mp hρ).2, hsqrt]
      ring
    rw [he]
    exact (mul_le_mul_of_nonneg_left hlow (by positivity)).trans_eq (by ring)
  have hh : (∑ ρ ∈ Zhi, (DusartSmoothing.RvM.zeroMult ρ : ℝ)*
      x^(ρ.re-1)*(1/|ρ.im|^19)) ≤ 1/(2*H^18) := by
    apply le_trans (Finset.sum_le_sum (fun ρ hρ => ?_)) hhigh
    have hβ : x^(ρ.re-1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx
      (by linarith [(hZ ρ (Finset.mem_filter.mp hρ).1).2.2])
    calc
      _ ≤ (DusartSmoothing.RvM.zeroMult ρ : ℝ)*1*(1/|ρ.im|^19) := by gcongr
      _ = _ := by ring
  have hsplit := Finset.sum_filter_add_sum_filter_not Z (fun ρ : ℂ => |ρ.im| ≤ H)
    (fun ρ => (DusartSmoothing.RvM.zeroMult ρ : ℝ)*x^(ρ.re-1)*(1/|ρ.im|^19))
  dsimp only [Zlo, Zhi] at hl hh
  rw [← hsplit]
  exact add_le_add hl hh

theorem weighted_tail_of_finite_rh (x T H : ℝ) (hx : 1 ≤ x)
    (hT : (10 : ℝ)^8 ≤ T) (hTH : T ≤ H) (hlog : Real.log H ≤ 22)
    (hRH : ∀ ρ : ℂ, DusartSmoothing.RvM.IsNontrivialZero ρ → |ρ.im| ≤ H → ρ.re = 1/2) :
    (∑' ρ : StrictHighAbsoluteZero T, (DusartSmoothing.RvM.zeroMult ρ.val : ℝ)*
      x^(ρ.val.re-1)*(1/|ρ.val.im|^19)) ≤ 1/(2*Real.sqrt x*T^18)+1/(2*H^18) := by
  classical
  apply Real.tsum_le_of_sum_le
  · intro ρ
    positivity
  · intro S
    let Z : Finset ℂ := S.image (fun ρ : StrictHighAbsoluteZero T => ρ.val)
    have hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ := by
      intro ρ hρ
      obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp hρ
      exact τ.property.1
    have hγ : ∀ ρ ∈ Z, T < |ρ.im| := by
      intro ρ hρ
      obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp hρ
      exact τ.property.2
    have h := finite_weighted_tail_of_finite_rh Z hZ x T H hx hT hTH hlog hγ hRH
    dsimp [Z] at h
    rw [Finset.sum_image (fun a _ b _ he => Subtype.val_injective he)] at h
    exact h

theorem absolute_tail_summable (H : ℝ) (hH : (10 : ℝ)^8 ≤ H) (hlog : Real.log H ≤ 22) :
    Summable (fun ρ : StrictHighAbsoluteZero H =>
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ)*(1/|ρ.val.im|^19)) := by
  classical
  apply summable_of_sum_le (c := 1/(2*H^18))
  · intro ρ
    positivity
  · intro S
    let Z : Finset ℂ := S.image (fun ρ : StrictHighAbsoluteZero H => ρ.val)
    have hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ := by
      intro ρ hρ
      obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp hρ
      exact τ.property.1
    have hγ : ∀ ρ ∈ Z, H < |ρ.im| := by
      intro ρ hρ
      obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp hρ
      exact τ.property.2
    have h := finite_absolute_tail Z hZ H hH hlog hγ
    dsimp [Z] at h
    rw [Finset.sum_image (fun a _ b _ he => Subtype.val_injective he)] at h
    exact h

theorem weighted_tail_summable (x T : ℝ) (hx : 1 ≤ x)
    (hT : (10 : ℝ)^8 ≤ T) (hlog : Real.log T ≤ 22) :
    Summable (fun ρ : StrictHighAbsoluteZero T =>
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ)*x^(ρ.val.re-1)*(1/|ρ.val.im|^19)) := by
  apply (absolute_tail_summable T hT hlog).of_nonneg_of_le
  · intro ρ
    positivity
  · intro ρ
    have hβ : x^(ρ.val.re-1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx
      (by linarith [ρ.property.1.2.2])
    calc
      _ ≤ (DusartSmoothing.RvM.zeroMult ρ.val : ℝ)*1*(1/|ρ.val.im|^19) := by gcongr
      _ = _ := by ring

end ShortPrimeIntervalZeroMoments


-- Inlined checked source: Solutions/ShortPrimeIntervalIncrementSeries18.lean

noncomputable section
open DusartSmoothing
namespace ShortPrimeIntervalIncrementSeries18
open ShortPrimeIntervalMellin18 (mu)
open ShortPrimeIntervalLowZeros18 (lowZeros mem_lowZeros)

def increment (X u delta : ℝ) (rho : NontrivialZetaZero) : ℂ :=
  (RvM.zeroMult rho.val : ℂ)*ShortPrimeIntervalIncrement18.kernel X u delta rho.val

def lowBound (X u delta N : ℝ) : ℝ :=
  u*Real.sqrt X*Real.exp (u/2)*Real.sqrt (1+delta)*N

def highFactor (X u delta : ℝ) : ℝ :=
  (Real.exp u+1)*(1+delta)^19*mu*X/delta^18

def highBound (X u delta T H : ℝ) : ℝ :=
  highFactor X u delta*(1/(2*Real.sqrt X*T^18)+1/(2*H^18))

theorem finite_increment_norm_bound (X u delta T H N : ℝ)
    (hX : 1 ≤ X) (hu : 0 ≤ u) (hd : 0 < delta)
    (hT : (10 : ℝ)^8 ≤ T) (hTH : T ≤ H) (hlog : Real.log H ≤ 22)
    (hRH : ∀ rho : ℂ, RvM.IsNontrivialZero rho → |rho.im| ≤ H → rho.re = 1/2)
    (hN : (∑ rho ∈ lowZeros T, (RvM.zeroMult rho.val : ℝ)) ≤ N)
    (S : Finset NontrivialZetaZero) :
    (∑ rho ∈ S, ‖increment X u delta rho‖) ≤
      lowBound X u delta N+highBound X u delta T H := by
  classical
  let Sl := S.filter (fun rho => |rho.val.im| ≤ T)
  let Sh := S.filter (fun rho => ¬|rho.val.im| ≤ T)
  have hX0 : 0 < X := by linarith
  have hl : (∑ rho ∈ Sl, ‖increment X u delta rho‖) ≤ lowBound X u delta N := by
    have hc : (∑ rho ∈ Sl, (RvM.zeroMult rho.val : ℝ)) ≤ N := by
      apply le_trans _ hN
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro rho hr
        exact (mem_lowZeros T rho).mpr (Finset.mem_filter.mp hr).2
      · intros
        positivity
    calc
      _ ≤ ∑ rho ∈ Sl, (RvM.zeroMult rho.val : ℝ)*
          (u*Real.sqrt X*Real.exp (u/2)*Real.sqrt (1+delta)) := by
        apply Finset.sum_le_sum
        intro rho hr
        rw [increment, norm_mul, Complex.norm_natCast]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply ShortPrimeIntervalIncrement18.norm_kernel_low X u delta hX0 hu hd.le rho.val
        exact hRH rho.val rho.property ((Finset.mem_filter.mp hr).2.trans hTH)
      _ = (∑ rho ∈ Sl, (RvM.zeroMult rho.val : ℝ))*
          (u*Real.sqrt X*Real.exp (u/2)*Real.sqrt (1+delta)) := by rw [Finset.sum_mul]
      _ ≤ lowBound X u delta N := by
        unfold lowBound
        nlinarith only [mul_le_mul_of_nonneg_right hc
          (show 0 ≤ u*Real.sqrt X*Real.exp (u/2)*Real.sqrt (1+delta) by positivity)]
  have hh : (∑ rho ∈ Sh, ‖increment X u delta rho‖) ≤ highBound X u delta T H := by
    let Z := Sh.image (fun rho : NontrivialZetaZero => rho.val)
    have hZ : ∀ rho ∈ Z, RvM.IsNontrivialZero rho := by
      intro rho hr
      obtain ⟨tau, _, rfl⟩ := Finset.mem_image.mp hr
      exact tau.property
    have hgamma : ∀ rho ∈ Z, T < |rho.im| := by
      intro rho hr
      obtain ⟨tau, ht, rfl⟩ := Finset.mem_image.mp hr
      exact lt_of_not_ge (Finset.mem_filter.mp ht).2
    have hmoment := ShortPrimeIntervalZeroMoments.finite_weighted_tail_of_finite_rh
      Z hZ X T H hX hT hTH hlog hgamma hRH
    dsimp only [Z] at hmoment
    rw [Finset.sum_image (fun a _ b _ he => Subtype.val_injective he)] at hmoment
    have hmu : 0 ≤ mu := by
      unfold ShortPrimeIntervalMellin18.mu ShortPrimeIntervalWeight18.derivativeRatio
      positivity
    have hfactor : 0 ≤ highFactor X u delta := by unfold highFactor; positivity
    calc
      _ ≤ ∑ rho ∈ Sh, highFactor X u delta*((RvM.zeroMult rho.val : ℝ)*
          X^(rho.val.re-1)*(1/|rho.val.im|^19)) := by
        apply Finset.sum_le_sum
        intro rho hr
        have hi := RvM.nontrivial_zero_abs_height rho.val rho.property
        have him : rho.val.im ≠ 0 := abs_pos.mp
          ((by positivity : (0 : ℝ) < 2*Real.pi).trans hi)
        have hk := ShortPrimeIntervalIncrement18.norm_kernel_high X u delta hX0 hu hd
          rho.val him rho.property.2.1.le rho.property.2.2.le
        rw [increment, norm_mul, Complex.norm_natCast]
        exact (mul_le_mul_of_nonneg_left hk (by positivity)).trans_eq (by unfold highFactor; ring)
      _ = highFactor X u delta*(∑ rho ∈ Sh, (RvM.zeroMult rho.val : ℝ)*
          X^(rho.val.re-1)*(1/|rho.val.im|^19)) := by rw [Finset.mul_sum]
      _ ≤ highBound X u delta T H := mul_le_mul_of_nonneg_left hmoment hfactor
  have hsplit := Finset.sum_filter_add_sum_filter_not S
    (fun rho : NontrivialZetaZero => |rho.val.im| ≤ T)
    (fun rho => ‖increment X u delta rho‖)
  dsimp only [Sl, Sh] at hl hh
  rw [← hsplit]
  exact add_le_add hl hh

theorem increment_norm_summable_bound (X u delta T H N : ℝ)
    (hX : 1 ≤ X) (hu : 0 ≤ u) (hd : 0 < delta)
    (hT : (10 : ℝ)^8 ≤ T) (hTH : T ≤ H) (hlog : Real.log H ≤ 22)
    (hRH : ∀ rho : ℂ, RvM.IsNontrivialZero rho → |rho.im| ≤ H → rho.re = 1/2)
    (hN : (∑ rho ∈ lowZeros T, (RvM.zeroMult rho.val : ℝ)) ≤ N) :
    Summable (fun rho => ‖increment X u delta rho‖) ∧
      ‖∑' rho : NontrivialZetaZero, increment X u delta rho‖ ≤
        lowBound X u delta N+highBound X u delta T H := by
  have hf := finite_increment_norm_bound X u delta T H N hX hu hd hT hTH hlog hRH hN
  have hs : Summable (fun rho => ‖increment X u delta rho‖) :=
    summable_of_sum_le (fun _ => norm_nonneg _) hf
  exact ⟨hs, (norm_tsum_le_tsum_norm hs).trans (Real.tsum_le_of_sum_le
    (fun _ => norm_nonneg _) hf)⟩

end ShortPrimeIntervalIncrementSeries18


-- Inlined checked source: Solutions/ShortPrimeIntervalMainTerm18.lean

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace ShortPrimeIntervalMainTerm18
open ShortPrimeIntervalWeight18

def f (t : ℝ) : ℝ := (4*t*(1-t))^18

def d2 (t : ℝ) : ℝ := iteratedDeriv 2 f t

def mass : ℝ := ∫ t in (0 : ℝ)..1, f t

def moment (k : ℕ) : ℚ :=
  qIntegral 19 (derivativeCoeff 2) (fun j => derivativeExponent 2 j + k) 0 1

theorem d2_continuous : Continuous d2 :=
  ContDiff.continuous_iteratedDeriv 2 weight_contDiff (by simp)

theorem real_moment (k : ℕ) :
    (∫ t in (0 : ℝ)..1, d2 t * t^k) = (moment k : ℝ) := by
  have heq (t : ℝ) : d2 t * t^k = ∑ j ∈ Finset.range 19,
      (derivativeCoeff 2 j : ℝ) * t^(derivativeExponent 2 j+k) := by
    unfold d2 f
    rw [iteratedDeriv_weight, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_add]
    ring
  simp_rw [heq]
  have h := integral_eq_qIntegral 19 (derivativeCoeff 2)
    (fun j => derivativeExponent 2 j+k) 0 1
  simp only [Rat.cast_zero, Rat.cast_one] at h
  convert h using 1 <;> rfl

theorem moment0 : moment 0 = 0 := by decide +kernel

theorem moment1 : moment 1 = 0 := by decide +kernel

theorem moment2 : moment 2 = 2*weightIntegral 0 1 := by decide +kernel

theorem moment3 : moment 3 = 3*weightIntegral 0 1 := by decide +kernel

theorem real_moment0 : (∫ t in (0 : ℝ)..1, d2 t) = 0 := by
  have h := real_moment 0
  simpa only [pow_zero, mul_one, moment0, Rat.cast_zero] using h

theorem real_moment1 : (∫ t in (0 : ℝ)..1, d2 t*t) = 0 := by
  have h := real_moment 1
  simpa only [pow_one, moment1, Rat.cast_zero] using h

theorem real_moment2 : (∫ t in (0 : ℝ)..1, d2 t*t^2) = 2*mass := by
  rw [real_moment, moment2]
  have h := integral_weight 0 1
  simp only [Rat.cast_zero, Rat.cast_one] at h
  dsimp only [mass, f]
  rw [h]
  push_cast
  rfl

theorem real_moment3 : (∫ t in (0 : ℝ)..1, d2 t*t^3) = 3*mass := by
  rw [real_moment, moment3]
  have h := integral_weight 0 1
  simp only [Rat.cast_zero, Rat.cast_one] at h
  dsimp only [mass, f]
  rw [h]
  push_cast
  rfl

/-- The cubic Perron main term becomes the expected weighted main term. -/
theorem cubic_main (A B : ℝ) :
    (∫ t in (0 : ℝ)..1, d2 t*(A+B*t)^3/6) = B^2*mass*(A+B/2) := by
  have hd := d2_continuous
  have heq : (fun t : ℝ => d2 t*(A+B*t)^3/6) =
      (fun t => (A^3/6)*d2 t + (A^2*B/2)*(d2 t*t) +
        (A*B^2/2)*(d2 t*t^2) + (B^3/6)*(d2 t*t^3)) := by funext t; ring
  rw [heq, intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_add]
  · simp_rw [intervalIntegral.integral_const_mul]
    rw [real_moment0, real_moment1, real_moment2, real_moment3]
    ring
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- The quadratic zeta-at-zero term is independent of the scale after division
by B^2, so it cancels between the two short-interval endpoints. -/
theorem quadratic_main (A B : ℝ) :
    (∫ t in (0 : ℝ)..1, d2 t*(A+B*t)^2/2) = B^2*mass := by
  have hd := d2_continuous
  have heq : (fun t : ℝ => d2 t*(A+B*t)^2/2) =
      (fun t => (A^2/2)*d2 t + (A*B)*(d2 t*t) + (B^2/2)*(d2 t*t^2)) := by funext t; ring
  rw [heq, intervalIntegral.integral_add, intervalIntegral.integral_add]
  · simp_rw [intervalIntegral.integral_const_mul]
    rw [real_moment0, real_moment1, real_moment2]
    ring
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

end ShortPrimeIntervalMainTerm18


-- Inlined checked source: Solutions/ShortPrimeIntervalWeightedPrimitive.lean

set_option maxHeartbeats 1000000

/-!
# The weighted second-primitive identity

This connects a smooth weighted Chebyshev count to the second primitive used
by the existing Perron explicit formula. The right derivative convention
preserves the closed upper endpoint of the prime-counting function.
-/

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace ShortPrimeIntervalWeightedPrimitive

noncomputable def step (c x : ℝ) : ℝ := if c ≤ x then 1 else 0

noncomputable def first (S : Finset ℕ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ S, a n * max (x-n) 0

noncomputable def second (S : Finset ℕ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ S, a n * (max (x-n) 0)^2 / 2

noncomputable def count (S : Finset ℕ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ S, a n * step n x

theorem step_mono (c : ℝ) : Monotone (step c) := by
  intro x y hxy
  unfold step
  split_ifs <;> linarith

theorem max_hasDerivWithinAt_right (c x : ℝ) :
    HasDerivWithinAt (fun y : ℝ => max (y-c) 0) (step c x) (Ioi x) x := by
  by_cases hcx : c ≤ x
  · rw [step, if_pos hcx]
    apply ((hasDerivAt_id x).sub_const c).hasDerivWithinAt.congr
    · intro y hy
      exact max_eq_left (by change x < y at hy; linarith)
    · exact max_eq_left (sub_nonneg.mpr hcx)
  · have hxc : x < c := lt_of_not_ge hcx
    have heq : (fun y : ℝ => max (y-c) 0) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [gt_mem_nhds hxc] with y hy
      exact max_eq_right (by linarith)
    have h := (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq heq
    simpa only [step, if_neg hcx] using h.hasDerivWithinAt

theorem second_kernel_hasDerivWithinAt_right (c x : ℝ) :
    HasDerivWithinAt (fun y : ℝ => (max (y-c) 0)^2 / 2)
      (max (x-c) 0) (Ioi x) x := by
  have h := ((max_hasDerivWithinAt_right c x).pow 2).div_const 2
  convert h using 1 <;> try rfl
  by_cases hcx : c ≤ x
  · simp [step, hcx]
  · simp [step, hcx, max_eq_right (by linarith : x-c ≤ 0)]

theorem first_continuous (S : Finset ℕ) (a : ℕ → ℝ) : Continuous (first S a) := by
  unfold first
  fun_prop

theorem second_continuous (S : Finset ℕ) (a : ℕ → ℝ) : Continuous (second S a) := by
  unfold second
  fun_prop

theorem first_hasDerivWithinAt_right (S : Finset ℕ) (a : ℕ → ℝ) (x : ℝ) :
    HasDerivWithinAt (first S a) (count S a x) (Ioi x) x := by
  have h := HasDerivWithinAt.sum (fun n (_ : n ∈ S) =>
    (max_hasDerivWithinAt_right (n : ℝ) x).const_mul (a n))
  convert h using 1 <;> try rfl
  funext t
  simp only [first, Finset.sum_apply]

theorem second_hasDerivWithinAt_right (S : Finset ℕ) (a : ℕ → ℝ) (x : ℝ) :
    HasDerivWithinAt (second S a) (first S a x) (Ioi x) x := by
  have h := HasDerivWithinAt.sum (fun n (_ : n ∈ S) =>
    (second_kernel_hasDerivWithinAt_right n x).const_mul (a n))
  convert h using 1 <;> try rfl
  funext t
  simp only [second, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem weighted_second_identity (P P' P'' f f' f'' : ℝ → ℝ)
    (hP : Continuous P) (hP' : Continuous P')
    (hPderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt P (P' t) (Ioi t) t)
    (hP'deriv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt P' (P'' t) (Ioi t) t)
    (hP'' : IntervalIntegrable P'' volume 0 1)
    (hf : Continuous f) (hf' : Continuous f') (hf'' : Continuous f'')
    (hfderiv : ∀ t, HasDerivAt f (f' t) t)
    (hf'deriv : ∀ t, HasDerivAt f' (f'' t) t)
    (hz : f 0 = 0) (ho : f 1 = 0) (hz' : f' 0 = 0) (ho' : f' 1 = 0) :
    (∫ t in (0 : ℝ)..1, f t * P'' t) = ∫ t in (0 : ℝ)..1, f'' t * P t := by
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    hf.continuousOn hP'.continuousOn
    (fun t _ => (hfderiv t).hasDerivWithinAt)
    (fun t ht => hP'deriv t (by simpa using ht))
    (hf'.intervalIntegrable 0 1) hP''
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    hf'.continuousOn hP.continuousOn
    (fun t _ => (hf'deriv t).hasDerivWithinAt)
    (fun t ht => hPderiv t (by simpa using ht))
    (hf''.intervalIntegrable 0 1) (hP'.intervalIntegrable 0 1)
  simp only [hz, ho, hz', ho', zero_mul, sub_self, zero_sub] at h1 h2
  linarith

theorem right_deriv_comp_affine (g g' : ℝ → ℝ)
    (hg : ∀ x, HasDerivWithinAt g (g' x) (Ioi x) x)
    (A B : ℝ) (hB : 0 < B) (t : ℝ) :
    HasDerivWithinAt (fun v => g (A+B*v)) (B*g' (A+B*t)) (Ioi t) t := by
  have ha : HasDerivAt (fun v : ℝ => A+B*v) B t := by
    convert (hasDerivAt_const t A).add ((hasDerivAt_id t).const_mul B) using 1 <;>
      first | rfl | simp only [zero_add, mul_one]
  have hm : MapsTo (fun v : ℝ => A+B*v) (Ioi t) (Ioi (A+B*t)) := by
    intro v hv
    change t < v at hv
    change A+B*t < A+B*v
    simpa only [add_comm] using add_lt_add_left (mul_lt_mul_of_pos_left hv hB) A
  have h := (hg (A+B*t)).comp t ha.hasDerivWithinAt hm
  convert h using 1 <;> first | rfl | ring

theorem count_affine_intervalIntegrable (S : Finset ℕ) (a : ℕ → ℝ)
    (A B : ℝ) (hB : 0 ≤ B) :
    IntervalIntegrable (fun t => count S a (A+B*t)) volume 0 1 := by
  have hm : Monotone (fun t : ℝ => A+B*t) := by
    intro u v huv
    dsimp
    nlinarith
  have h := IntervalIntegrable.sum (μ := volume) S (fun n (_ : n ∈ S) =>
    (((step_mono n).comp hm).intervalIntegrable (a := (0 : ℝ)) (b := 1)).const_mul (a n))
  convert h using 1 <;> try rfl
  funext t
  simp only [count, Finset.sum_apply, Function.comp_apply]

/-- The actual finite counting sum and its second primitive, after an affine
change of variables. The finite sum includes the endpoint n=A+B*t. -/
theorem weighted_finite_count (S : Finset ℕ) (a : ℕ → ℝ) (A B : ℝ) (hB : 0 < B)
    (f f' f'' : ℝ → ℝ) (hf : Continuous f) (hf' : Continuous f') (hf'' : Continuous f'')
    (hfderiv : ∀ t, HasDerivAt f (f' t) t)
    (hf'deriv : ∀ t, HasDerivAt f' (f'' t) t)
    (hz : f 0 = 0) (ho : f 1 = 0) (hz' : f' 0 = 0) (ho' : f' 1 = 0) :
    (∫ t in (0 : ℝ)..1, f'' t * second S a (A+B*t)) =
      B^2 * (∫ t in (0 : ℝ)..1, f t * count S a (A+B*t)) := by
  have hd2 (t : ℝ) : HasDerivWithinAt (fun v => second S a (A+B*v))
      (B*first S a (A+B*t)) (Ioi t) t :=
    right_deriv_comp_affine _ _ (second_hasDerivWithinAt_right S a) A B hB t
  have hd1 (t : ℝ) : HasDerivWithinAt (fun v => B*first S a (A+B*v))
      (B^2*count S a (A+B*t)) (Ioi t) t := by
    have h := (right_deriv_comp_affine _ _ (first_hasDerivWithinAt_right S a) A B hB t).const_mul B
    convert h using 1 <;> first | rfl | ring
  have h := weighted_second_identity (fun t => second S a (A+B*t))
    (fun t => B*first S a (A+B*t)) (fun t => B^2*count S a (A+B*t))
    f f' f''
    ((second_continuous S a).comp (by fun_prop))
    (((first_continuous S a).comp (by fun_prop)).const_mul B)
    (fun t _ => hd2 t) (fun t _ => hd1 t)
    ((count_affine_intervalIntegrable S a A B hB.le).const_mul (B^2))
    hf hf' hf'' hfderiv hf'deriv hz ho hz' ho'
  have heq (t : ℝ) : f t * (B^2*count S a (A+B*t)) =
      B^2*(f t * count S a (A+B*t)) := by ring
  simp_rw [heq] at h
  rw [intervalIntegral.integral_const_mul] at h
  exact h.symm

theorem count_vonMangoldt_eq_psi (N : ℕ) (x : ℝ) (hx : 0 ≤ x) (hN : x ≤ N) :
    count (Finset.Ioc 0 N) ArithmeticFunction.vonMangoldt x = Chebyshev.psi x := by
  classical
  have hfloor : ⌊x⌋₊ ≤ N := Nat.floor_le_of_le hN
  have hsub : Finset.Ioc 0 ⌊x⌋₊ ⊆ Finset.Ioc 0 N := Finset.Ioc_subset_Ioc le_rfl hfloor
  unfold count Chebyshev.psi
  calc
    _ = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * step n x := by
      symm
      apply Finset.sum_subset hsub
      intro n hn hn'
      have hnf : ¬n ≤ ⌊x⌋₊ := by
        intro hnf
        exact hn' (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1, hnf⟩)
      have hnx : ¬(n : ℝ) ≤ x := by
        intro hnx
        exact hnf ((Nat.le_floor_iff hx).mpr hnx)
      simp only [step, if_neg hnx, mul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx).mp (Finset.mem_Ioc.mp hn).2
      simp only [step, if_pos hnx, mul_one]

/-- Weighted psi is the second primitive paired with the second derivative of
the test function. This is the exact left side of the existing Perron formula. -/
theorem weighted_psi (N : ℕ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 < B) (hN : A+B ≤ N)
    (f f' f'' : ℝ → ℝ) (hf : Continuous f) (hf' : Continuous f') (hf'' : Continuous f'')
    (hfderiv : ∀ t, HasDerivAt f (f' t) t)
    (hf'deriv : ∀ t, HasDerivAt f' (f'' t) t)
    (hz : f 0 = 0) (ho : f 1 = 0) (hz' : f' 0 = 0) (ho' : f' 1 = 0) :
    (∫ t in (0 : ℝ)..1, f'' t * second (Finset.Ioc 0 N) ArithmeticFunction.vonMangoldt (A+B*t)) =
      B^2 * (∫ t in (0 : ℝ)..1, f t * Chebyshev.psi (A+B*t)) := by
  rw [weighted_finite_count (Finset.Ioc 0 N) ArithmeticFunction.vonMangoldt A B hB
    f f' f'' hf hf' hf'' hfderiv hf'deriv hz ho hz' ho']
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
  change f t * count (Finset.Ioc 0 N) ArithmeticFunction.vonMangoldt (A+B*t) =
    f t * Chebyshev.psi (A+B*t)
  rw [count_vonMangoldt_eq_psi N (A+B*t) (by nlinarith [ht'.1]) (by nlinarith [ht'.2])]

end ShortPrimeIntervalWeightedPrimitive


-- Inlined checked source: Solutions/ShortPrimeIntervalWeightedSeries.lean

noncomputable section
open MeasureTheory Set

namespace ShortPrimeIntervalWeightedSeries

/-- Absolute uniform bounds on a compact interval justify weighting and
integrating the zero series. The index set may be any countable type. -/
theorem weighted_integral_tsum {ι : Type*} [Countable ι]
    (K : ι → ℝ → ℂ) (hK : ∀ i, ContinuousOn (K i) (Icc (0 : ℝ) 1))
    (cap : ι → ℝ) (hc : Summable cap)
    (hbound : ∀ i t, t ∈ Icc (0 : ℝ) 1 → ‖K i t‖ ≤ cap i)
    (g : ℝ → ℂ) (hg : ContinuousOn g (Icc (0 : ℝ) 1)) :
    (∫ t in (0 : ℝ)..1, g t * (∑' i, K i t)) =
      ∑' i, (∫ t in (0 : ℝ)..1, g t * K i t) := by
  let G (i : ι) (t : ℝ) : ℂ := g t * K i t
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hg' : ContinuousOn g (uIcc (0 : ℝ) 1) := by simpa using hg
  have hGi (i : ι) : IntervalIntegrable (G i) volume 0 1 := by
    have hKi : ContinuousOn (K i) (uIcc (0 : ℝ) 1) := by simpa using hK i
    exact (hg'.mul hKi).intervalIntegrable
  have hnorm (i : ι) : (∫ t in Ioc (0 : ℝ) 1, ‖G i t‖) ≤
      cap i * (∫ t in (0 : ℝ)..1, ‖g t‖) := by
    rw [← intervalIntegral.integral_of_le h01, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on h01 (hGi i).norm
      ((hg'.norm.const_mul (cap i)).intervalIntegrable)
    intro t ht
    dsimp [G]
    rw [norm_mul, mul_comm (cap i)]
    exact mul_le_mul_of_nonneg_left (hbound i t ht) (norm_nonneg _)
  have hsum : Summable (fun i => ∫ t in Ioc (0 : ℝ) 1, ‖G i t‖) :=
    (hc.mul_right (∫ t in (0 : ℝ)..1, ‖g t‖)).of_nonneg_of_le
      (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hnorm
  have h := MeasureTheory.integral_tsum_of_summable_integral_norm
    (fun i => (hGi i).1) hsum
  simp_rw [← tsum_mul_left, intervalIntegral.integral_of_le h01]
  exact h.symm

end ShortPrimeIntervalWeightedSeries


-- Inlined checked source: Solutions/ShortPrimeIntervalWeightedFormula18.lean

noncomputable section
open MeasureTheory Set
namespace ShortPrimeIntervalWeightedFormula18
open ShortPrimeIntervalMainTerm18 (f d2 mass)
open ShortPrimeIntervalWeightedPrimitive (second)

theorem cubic_main_complex (A B : ℝ) :
    (∫ t in (0 : ℝ)..1, (d2 t : ℂ)*(((A+B*t : ℝ) : ℂ)^3/6)) =
      (B : ℂ)^2*(mass : ℂ)*((A+B/2 : ℝ) : ℂ) := by
  calc
    _ = ∫ t in (0 : ℝ)..1, ((d2 t*(A+B*t)^3/6 : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro t _
      push_cast
      ring
    _ = ((∫ t in (0 : ℝ)..1, d2 t*(A+B*t)^3/6 : ℝ) : ℂ) := intervalIntegral.integral_ofReal
    _ = _ := by rw [ShortPrimeIntervalMainTerm18.cubic_main]; push_cast; ring

theorem quadratic_main_complex (A B : ℝ) :
    (∫ t in (0 : ℝ)..1, (d2 t : ℂ)*(((A+B*t : ℝ) : ℂ)^2/2)) =
      (B : ℂ)^2*(mass : ℂ) := by
  calc
    _ = ∫ t in (0 : ℝ)..1, ((d2 t*(A+B*t)^2/2 : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro t _
      push_cast
      ring
    _ = ((∫ t in (0 : ℝ)..1, d2 t*(A+B*t)^2/2 : ℝ) : ℂ) := intervalIntegral.integral_ofReal
    _ = _ := by rw [ShortPrimeIntervalMainTerm18.quadratic_main]; push_cast; ring

theorem weighted_psi_cast (N : ℕ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 < B) (hN : A+B ≤ N) :
    (B : ℂ)^2 * ((∫ t in (0 : ℝ)..1, f t*Chebyshev.psi (A+B*t) : ℝ) : ℂ) =
      ∫ t in (0 : ℝ)..1, (d2 t : ℂ)*
        (second (Finset.Ioc 0 N) ArithmeticFunction.vonMangoldt (A+B*t) : ℂ) := by
  have hf : Continuous f := by unfold f; fun_prop
  have hf' : Continuous (iteratedDeriv 1 f) :=
    ContDiff.continuous_iteratedDeriv 1 ShortPrimeIntervalWeight18.weight_contDiff (by simp)
  have hf'' := ShortPrimeIntervalMainTerm18.d2_continuous
  have hd (n : ℕ) (t : ℝ) : HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n+1) f t) t := by
    have h := ContDiff.differentiable_iteratedDeriv n ShortPrimeIntervalWeight18.weight_contDiff (by simp)
    rw [iteratedDeriv_succ]
    convert (h t).hasDerivAt using 1 <;> rfl
  have h := ShortPrimeIntervalWeightedPrimitive.weighted_psi N A B hA hB hN
    f (iteratedDeriv 1 f) d2 hf hf' hf''
    (fun t => by simpa only [iteratedDeriv_zero] using hd 0 t)
    (fun t => hd 1 t)
    (by norm_num [f]) (by norm_num [f])
    (ShortPrimeIntervalWeight18.lower_endpoint_vanishing 1 (by norm_num))
    (ShortPrimeIntervalWeight18.upper_endpoint_vanishing 1 (by norm_num))
  have hc := congrArg Complex.ofReal h
  push_cast at hc
  rw [← intervalIntegral.integral_ofReal] at hc
  calc
    _ = ∫ t in (0 : ℝ)..1, ((d2 t *
      second (Finset.Ioc 0 N) ArithmeticFunction.vonMangoldt (A+B*t) : ℝ) : ℂ) := hc.symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t _
      push_cast
      rfl

/-- Transferring a second-primitive explicit formula to the concrete weighted
psi integral. The kernel continuity/summability and exact primitive formula
are explicit inputs; actual zeta kernels can be substituted directly. -/
theorem weighted_explicit_formula {ι : Type*} [Countable ι]
    (N : ℕ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 < B) (hN : A+B ≤ N)
    (L : ℂ) (K : ι → ℝ → ℂ)
    (hK : ∀ i, ContinuousOn (K i) (Icc (0 : ℝ) 1))
    (cap : ι → ℝ) (hc : Summable cap)
    (hbound : ∀ i t, t ∈ Icc (0 : ℝ) 1 → ‖K i t‖ ≤ cap i)
    (R : ℝ → ℂ)
    (hformula : ∀ t ∈ Icc (0 : ℝ) 1,
      (second (Finset.Ioc 0 N) ArithmeticFunction.vonMangoldt (A+B*t) : ℂ) =
        ((A+B*t : ℝ) : ℂ)^3/6 - ((A+B*t : ℝ) : ℂ)^2/2*L -
          (∑' i, K i t) + R t) :
    ((∫ t in (0 : ℝ)..1, f t*Chebyshev.psi (A+B*t) : ℝ) : ℂ) =
      (mass : ℂ)*((A+B/2 : ℝ) : ℂ) - (mass : ℂ)*L -
        (∑' i, (∫ t in (0 : ℝ)..1, (d2 t : ℂ)*K i t))/(B : ℂ)^2 +
        (∫ t in (0 : ℝ)..1, (d2 t : ℂ)*R t)/(B : ℂ)^2 := by
  let P : ℝ → ℂ := fun t => second (Finset.Ioc 0 N) ArithmeticFunction.vonMangoldt (A+B*t)
  let Q3 : ℝ → ℂ := fun t => ((A+B*t : ℝ) : ℂ)^3/6
  let Q2 : ℝ → ℂ := fun t => ((A+B*t : ℝ) : ℂ)^2/2*L
  let Z : ℝ → ℂ := fun t => ∑' i, K i t
  let g : ℝ → ℂ := fun t => d2 t
  have hg : Continuous g := Complex.continuous_ofReal.comp ShortPrimeIntervalMainTerm18.d2_continuous
  have hP : Continuous P := Complex.continuous_ofReal.comp
    ((ShortPrimeIntervalWeightedPrimitive.second_continuous _ _).comp (by fun_prop))
  have hQ3 : Continuous Q3 := by dsimp [Q3]; fun_prop
  have hQ2 : Continuous Q2 := by dsimp [Q2]; fun_prop
  have hZ : ContinuousOn Z (Icc (0 : ℝ) 1) := continuousOn_tsum hK hc hbound
  have hR : ContinuousOn R (Icc (0 : ℝ) 1) := by
    apply (((hP.continuousOn.sub hQ3.continuousOn).add hQ2.continuousOn).add hZ).congr
    intro t ht
    have h := hformula t ht
    change P t = Q3 t-Q2 t-Z t+R t at h
    have he : R t = P t-Q3 t+Q2 t+Z t := by linear_combination -h
    simpa only [Pi.sub_apply, Pi.add_apply] using he
  have hZ' : ContinuousOn Z (uIcc (0 : ℝ) 1) := by simpa using hZ
  have hR' : ContinuousOn R (uIcc (0 : ℝ) 1) := by simpa using hR
  have hI3 := (hg.mul hQ3).intervalIntegrable (μ := volume) (0 : ℝ) 1
  have hI2 := (hg.mul hQ2).intervalIntegrable (μ := volume) (0 : ℝ) 1
  have hIZ := (hg.continuousOn.mul hZ').intervalIntegrable (μ := volume)
  have hIR := (hg.continuousOn.mul hR').intervalIntegrable (μ := volume)
  change IntervalIntegrable (fun t => g t*Q3 t) volume 0 1 at hI3
  change IntervalIntegrable (fun t => g t*Q2 t) volume 0 1 at hI2
  change IntervalIntegrable (fun t => g t*Z t) volume 0 1 at hIZ
  change IntervalIntegrable (fun t => g t*R t) volume 0 1 at hIR
  have heq : (∫ t in (0 : ℝ)..1, g t*P t) =
      (∫ t in (0 : ℝ)..1, g t*Q3 t) - (∫ t in (0 : ℝ)..1, g t*Q2 t) -
        (∫ t in (0 : ℝ)..1, g t*Z t) + (∫ t in (0 : ℝ)..1, g t*R t) := by
    calc
      _ = ∫ t in (0 : ℝ)..1, g t*Q3 t-g t*Q2 t-g t*Z t+g t*R t := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
        have h := congrArg (fun z => g t*z) (hformula t ht')
        dsimp [P, Q3, Q2, Z] at h ⊢
        linear_combination h
      _ = _ := by
        rw [intervalIntegral.integral_add ((hI3.sub hI2).sub hIZ) hIR,
          intervalIntegral.integral_sub (hI3.sub hI2) hIZ, intervalIntegral.integral_sub hI3 hI2]
  have hq3 : (∫ t in (0 : ℝ)..1, g t*Q3 t) =
      (B : ℂ)^2*(mass : ℂ)*((A+B/2 : ℝ) : ℂ) := cubic_main_complex A B
  have hq2 : (∫ t in (0 : ℝ)..1, g t*Q2 t) = (B : ℂ)^2*(mass : ℂ)*L := by
    have he (t : ℝ) : g t*Q2 t = (g t*(((A+B*t : ℝ) : ℂ)^2/2))*L := by dsimp [Q2]; ring
    simp_rw [he]
    rw [intervalIntegral.integral_mul_const]
    rw [show (∫ t in (0 : ℝ)..1, g t*(((A+B*t : ℝ) : ℂ)^2/2)) =
      (B : ℂ)^2*(mass : ℂ) from quadratic_main_complex A B]
  have hz := ShortPrimeIntervalWeightedSeries.weighted_integral_tsum K hK cap hc hbound g hg.continuousOn
  rw [hq3, hq2, hz] at heq
  have hp := weighted_psi_cast N A B hA hB hN
  change (B : ℂ)^2*((∫ t in (0 : ℝ)..1, f t*Chebyshev.psi (A+B*t) : ℝ) : ℂ) =
    ∫ t in (0 : ℝ)..1, g t*P t at hp
  have hB0 : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hB.ne'
  apply mul_left_cancel₀ (pow_ne_zero 2 hB0)
  calc
    _ = _ := hp.trans heq
    _ = _ := by dsimp [g]; field_simp [hB0]

end ShortPrimeIntervalWeightedFormula18


-- Inlined checked source: Solutions/ShortPrimeIntervalActualFormula18.lean

noncomputable section
open MeasureTheory Set
namespace ShortPrimeIntervalActualFormula18
open DusartSmoothing
open ShortPrimeIntervalMainTerm18 (f d2 mass)

theorem nontrivial_zeros_countable : Countable NontrivialZetaZero := by
  have hs : {ρ : ℂ | RvM.IsNontrivialZero ρ}.Countable := by
    apply (Set.countable_iUnion (fun n : ℕ =>
      (RvM.finite_symmetric_zero_window (n : ℝ)).countable)).mono
    intro ρ hρ
    exact Set.mem_iUnion.mpr ⟨⌈|ρ.im|⌉₊, hρ, Nat.le_ceil _⟩
  exact hs.to_subtype

theorem quadratic_kernel_continuous (rho : ℂ) (hr : 0 < rho.re) (A B : ℝ) :
    Continuous (fun t : ℝ => quadraticKernel (A+B*t) rho) := by
  have hcp := Complex.continuous_ofReal_cpow_const
    (show 0 < (rho+2).re by simp; linarith)
  unfold quadraticKernel
  exact (hcp.comp (by fun_prop)).div_const _

theorem quadratic_kernel_norm_mono (rho : ℂ) (hr : 0 < rho.re)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ‖quadraticKernel a rho‖ ≤ ‖quadraticKernel b rho‖ := by
  have hb : 0 < b := ha.trans_le hab
  unfold quadraticKernel
  rw [norm_div, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ha,
    Complex.norm_cpow_eq_rpow_re_of_pos hb]
  exact div_le_div_of_nonneg_right
    (Real.rpow_le_rpow ha.le hab (by simp; linarith)) (norm_nonneg _)

/-- The published second-primitive formula with actual zeta kernels, transferred
to the concrete smoothing weight. No RH hypothesis occurs in this formula. -/
theorem weighted_psi_actual (A B : ℝ) (hA : 1 ≤ A) (hB : 0 < B) :
    ((∫ t in (0 : ℝ)..1, f t*Chebyshev.psi (A+B*t) : ℝ) : ℂ) =
      (mass : ℂ)*((A+B/2 : ℝ) : ℂ) - (mass : ℂ)*logDeriv riemannZeta 0 -
        (∑' ρ : NontrivialZetaZero, (∫ t in (0 : ℝ)..1,
          (d2 t : ℂ)*((RvM.zeroMult ρ.val : ℂ)*quadraticKernel (A+B*t) ρ.val)))/(B : ℂ)^2 +
        (∫ t in (0 : ℝ)..1, (d2 t : ℂ)*perronLeftRemainder (A+B*t))/(B : ℂ)^2 := by
  letI : Countable NontrivialZetaZero := nontrivial_zeros_countable
  let K : NontrivialZetaZero → ℝ → ℂ := fun ρ t =>
    (RvM.zeroMult ρ.val : ℂ)*quadraticKernel (A+B*t) ρ.val
  let cap : NontrivialZetaZero → ℝ := fun ρ =>
    ‖(RvM.zeroMult ρ.val : ℂ)*quadraticKernel (A+B) ρ.val‖
  have hK (ρ : NontrivialZetaZero) : ContinuousOn (K ρ) (Icc (0 : ℝ) 1) :=
    ((quadratic_kernel_continuous ρ.val ρ.property.2.1 A B).const_mul _).continuousOn
  have hc : Summable cap :=
    actual_quadratic_zero_series_absolutely_summable (A+B) (by linarith)
  have hb (ρ : NontrivialZetaZero) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖K ρ t‖ ≤ cap ρ := by
    dsimp [K, cap]
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left
      (quadratic_kernel_norm_mono ρ.val ρ.property.2.1 (A+B*t) (A+B)
        (by nlinarith [ht.1]) (by nlinarith [ht.2])) (norm_nonneg _)
  let N : ℕ := ⌈A+B⌉₊
  have hN : A+B ≤ N := Nat.le_ceil _
  apply ShortPrimeIntervalWeightedFormula18.weighted_explicit_formula N A B
    (by linarith) hB hN (logDeriv riemannZeta 0) K hK cap hc hb
    (fun t => perronLeftRemainder (A+B*t))
  intro t ht
  have htlo : 1 ≤ A+B*t := by nlinarith [ht.1]
  have hthi : A+B*t ≤ N := le_trans (by nlinarith [ht.2]) hN
  have h := secondPsiPrimitive_explicit_formula N (A+B*t) htlo hthi
  convert h using 1 <;> rfl

end ShortPrimeIntervalActualFormula18


-- Inlined checked source: Solutions/ShortPrimeIntervalNormalizedFormula18.lean

noncomputable section
open MeasureTheory
namespace ShortPrimeIntervalNormalizedFormula18
open DusartSmoothing
open ShortPrimeIntervalMellin18 (f F mass mass_pos)
open ShortPrimeIntervalKernelMellin18 (moment)

def meanPsi (X delta : ℝ) : ℂ :=
  ((∫ t in (0 : ℝ)..1, f t*Chebyshev.psi (X+X*delta*t) : ℝ) : ℂ)/(mass : ℂ)

def term (X delta : ℝ) (rho : NontrivialZetaZero) : ℂ :=
  (RvM.zeroMult rho.val : ℂ)*((X : ℂ)^rho.val/rho.val)*(moment delta rho.val/(mass : ℂ))

def remainder (X delta : ℝ) : ℂ :=
  (∫ t in (0 : ℝ)..1, F 2 t*perronLeftRemainder (X+X*delta*t))/
    (((X*delta : ℝ) : ℂ)^2*(mass : ℂ))

def integralTerm (X delta : ℝ) (rho : NontrivialZetaZero) : ℂ :=
  ∫ t in (0 : ℝ)..1, F 2 t*((RvM.zeroMult rho.val : ℂ)*
    quadraticKernel (X+X*delta*t) rho.val)

theorem term_eq_integral (X delta : ℝ) (hX : 0 < X) (hd : 0 < delta)
    (rho : NontrivialZetaZero) :
    term X delta rho = integralTerm X delta rho/
      (((X*delta : ℝ) : ℂ)^2*(mass : ℂ)) := by
  have hi : rho.val.im ≠ 0 := by
    have h := RvM.nontrivial_zero_abs_height rho.val rho.property
    exact abs_pos.mp (lt_trans (by positivity : (0 : ℝ) < 2*Real.pi) h)
  have hk := ShortPrimeIntervalKernelMellin18.quadratic_kernel_mellin X delta hX hd
    rho.val rho.property.2.1 hi
  have he : integralTerm X delta rho = (RvM.zeroMult rho.val : ℂ)*
      (∫ t in (0 : ℝ)..1, F 2 t*quadraticKernel (X+X*delta*t) rho.val) := by
    unfold integralTerm
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    ring
  rw [he, div_mul_eq_div_div, mul_div_assoc, hk]
  unfold term
  ring

theorem integralTerm_summable (X delta : ℝ) (hX : 1 ≤ X) (hd : 0 < delta) :
    Summable (integralTerm X delta) := by
  let cap : NontrivialZetaZero → ℝ := fun rho =>
    ‖(RvM.zeroMult rho.val : ℂ)*quadraticKernel (X+X*delta) rho.val‖
  have hc : Summable cap := actual_quadratic_zero_series_absolutely_summable
    (X+X*delta) (by nlinarith)
  have hb (rho : NontrivialZetaZero) : ‖integralTerm X delta rho‖ ≤
      cap rho*(∫ t in (0 : ℝ)..1, ‖F 2 t‖) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le (a := (0 : ℝ)) (b := 1)
      (f := fun t => F 2 t*((RvM.zeroMult rho.val : ℂ)*
        quadraticKernel (X+X*delta*t) rho.val))
      (g := fun t => cap rho*‖F 2 t‖) (by norm_num)
      (Filter.Eventually.of_forall fun t ht => by
        rw [norm_mul, mul_comm (cap rho)]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        dsimp only [cap]
        rw [norm_mul, norm_mul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply ShortPrimeIntervalActualFormula18.quadratic_kernel_norm_mono
          rho.val rho.property.2.1 _ _
        · have hXd : 0 ≤ X*delta := mul_nonneg (by linarith) hd.le
          nlinarith only [hX, mul_nonneg hXd ht.1.le]
        · have hXd : 0 ≤ X*delta := mul_nonneg (by linarith) hd.le
          nlinarith only [mul_nonneg hXd (sub_nonneg.mpr ht.2)])
      (((ShortPrimeIntervalMellin18.F_continuous 2).norm.const_mul (cap rho)).intervalIntegrable
        (μ := volume) 0 1)
    rw [intervalIntegral.integral_const_mul] at h
    exact h
  exact Summable.of_norm_bounded (hc.mul_right (∫ t in (0 : ℝ)..1, ‖F 2 t‖)) hb

theorem term_summable (X delta : ℝ) (hX : 1 ≤ X) (hd : 0 < delta) :
    Summable (term X delta) := by
  have h := (integralTerm_summable X delta hX hd).div_const
    (((X*delta : ℝ) : ℂ)^2*(mass : ℂ))
  exact h.congr (fun rho => (term_eq_integral X delta (by linarith) hd rho).symm)

theorem normalized_formula (X delta : ℝ) (hX : 1 ≤ X) (hd : 0 < delta) :
    meanPsi X delta = ((X*(1+delta/2) : ℝ) : ℂ) - logDeriv riemannZeta 0 -
      (∑' rho : NontrivialZetaZero, term X delta rho) + remainder X delta := by
  have he : (∑' rho : NontrivialZetaZero, term X delta rho) =
      (∑' rho : NontrivialZetaZero, integralTerm X delta rho)/
        (((X*delta : ℝ) : ℂ)^2*(mass : ℂ)) := by
    simp_rw [term_eq_integral X delta (by linarith) hd]
    exact (tsum_div_const (f := integralTerm X delta)
      (a := ((X*delta : ℝ) : ℂ)^2*(mass : ℂ)))
  rw [he]
  have ha := ShortPrimeIntervalActualFormula18.weighted_psi_actual X (X*delta) hX
    (by positivity)
  change ((∫ t in (0 : ℝ)..1, f t*Chebyshev.psi (X+X*delta*t) : ℝ) : ℂ) =
    (mass : ℂ)*((X+X*delta/2 : ℝ) : ℂ) - (mass : ℂ)*logDeriv riemannZeta 0 -
      (∑' rho : NontrivialZetaZero, integralTerm X delta rho)/((X*delta : ℝ) : ℂ)^2 +
      (∫ t in (0 : ℝ)..1, F 2 t*perronLeftRemainder (X+X*delta*t))/((X*delta : ℝ) : ℂ)^2 at ha
  rw [meanPsi, ha]
  unfold remainder
  push_cast
  have hm : (mass : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr mass_pos.ne'
  field_simp
  <;> ring

end ShortPrimeIntervalNormalizedFormula18


-- Inlined checked source: Solutions/ShortPrimeIntervalRemainder18.lean

noncomputable section
namespace ShortPrimeIntervalRemainder18
open DusartSmoothing
open ShortPrimeIntervalMellin18 (mass mass_pos)
open ShortPrimeIntervalNormalizedFormula18 (remainder)

def bound (X delta : ℝ) : ℝ := 32768*(1+delta)^2/(Real.sqrt X*delta^2)

theorem norm_remainder_le (X delta : ℝ) (hX : 0 < X) (hd : 0 < delta) :
    ‖remainder X delta‖ ≤ bound X delta := by
  have hm : 0 < mass := mass_pos
  have hp : X^(3/2 : ℝ) = X*Real.sqrt X := by
    rw [show (3/2 : ℝ) = 1+1/2 by ring, Real.rpow_add hX, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have hr (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ‖perronLeftRemainder (X+X*delta*t)‖ ≤ 128*(X*Real.sqrt X)*(1+delta)^2 := by
    have hXd : 0 ≤ X*delta := mul_nonneg hX.le hd.le
    have htpos : 0 < X+X*delta*t := by
      nlinarith only [hX, mul_nonneg hXd ht.1]
    apply (norm_perronLeftRemainder _ htpos).trans
    have hab : X+X*delta*t ≤ X*(1+delta) := by
      nlinarith only [mul_nonneg hXd (sub_nonneg.mpr ht.2)]
    have hbase : (1 : ℝ) ≤ 1+delta := by linarith
    calc
      _ ≤ 128*(X*(1+delta))^(3/2 : ℝ) := by gcongr
      _ = 128*X^(3/2 : ℝ)*(1+delta)^(3/2 : ℝ) := by
        rw [Real.mul_rpow hX.le (by linarith : 0 ≤ 1+delta)]; ring
      _ ≤ 128*X^(3/2 : ℝ)*(1+delta)^2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)
      _ = _ := by rw [hp]
  have h := ShortPrimeIntervalMellin18.weighted_remainder_bound
    (fun t => perronLeftRemainder (X+X*delta*t))
    (128*(X*Real.sqrt X)*(1+delta)^2) (by positivity) hr
  rw [remainder, norm_div, norm_mul, norm_pow,
    Complex.norm_of_nonneg (mul_pos hX hd).le, Complex.norm_of_nonneg mass_pos.le]
  apply le_trans (div_le_div_of_nonneg_right h (by positivity))
  apply le_of_eq
  unfold bound
  have hs : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have hsq := Real.sq_sqrt hX.le
  field_simp
  rw [← hsq, Real.sqrt_sq (Real.sqrt_nonneg X)]
  ring

end ShortPrimeIntervalRemainder18


-- Inlined checked source: Solutions/ShortPrimeIntervalBudgets18.lean

noncomputable section
namespace ShortPrimeIntervalBudgets18
open ShortPrimeIntervalIncrementSeries18 (lowBound highBound highFactor)
open ShortPrimeIntervalMellin18 (mu)
open ShortPrimeIntervalRemainder18 (bound)

abbrev u : ℝ := 1/533000000
abbrev delta : ℝ := 18*u
abbrev T : ℝ := 1100000000
abbrev H : ℝ := 3290000000
abbrev c : ℝ := 10001/10000

theorem exp_u_le : Real.exp u ≤ c := by
  exact (Real.exp_bound_div_one_sub_of_interval (by norm_num : 0 ≤ u)
    (by norm_num : u < 1)).trans (by norm_num [u, c])

theorem delta_le : 1+delta ≤ c := by norm_num [delta, u, c]

theorem sqrt_delta_le : Real.sqrt (1+delta) ≤ c := by
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num [delta, u, c]

theorem log_H_le : Real.log H ≤ 22 := by
  have he : (271/100 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 271/100) he 22
  rw [← Real.exp_nat_mul] at h
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < H)).mpr
  exact (show H ≤ (271/100 : ℝ)^22 by norm_num [H]).trans
    (by simpa only [Nat.cast_ofNat, mul_one] using h)

theorem sqrt_X_ge (X : ℝ) (hX : (99/100 : ℝ)*10^20 ≤ X) :
    (9900000000 : ℝ) ≤ Real.sqrt X := by
  apply Real.le_sqrt_of_sq_le
  norm_num at hX ⊢
  linarith

theorem low_budget (X : ℝ) (hX : (99/100 : ℝ)*10^20 ≤ X) :
    lowBound X u delta 7854000000 ≤ (4/5 : ℝ)*u*X := by
  have hX0 : 0 ≤ X := by norm_num at hX; linarith
  have hsq := Real.sq_sqrt hX0
  have hs := sqrt_X_ge X hX
  have he : Real.exp (u/2) ≤ c :=
    (Real.exp_le_exp.mpr (by norm_num : u/2 ≤ u)).trans exp_u_le
  unfold lowBound
  calc
    _ ≤ u*Real.sqrt X*c*c*7854000000 := by gcongr; exact sqrt_delta_le
    _ ≤ (4/5 : ℝ)*u*Real.sqrt X*9900000000 := by
      have hn : c*c*(7854000000 : ℝ) ≤ (4/5 : ℝ)*9900000000 := by norm_num [c]
      nlinarith only [mul_le_mul_of_nonneg_left hn (show 0 ≤ u*Real.sqrt X by positivity)]
    _ ≤ (4/5 : ℝ)*u*Real.sqrt X*Real.sqrt X := by gcongr
    _ = _ := by nlinarith only [hsq]

theorem high_budget (X : ℝ) (hX : (99/100 : ℝ)*10^20 ≤ X) :
    highBound X u delta T H ≤ (13/100 : ℝ)*u*X := by
  have hX0 : 0 ≤ X := by norm_num at hX; linarith
  have hs := sqrt_X_ge X hX
  have hmu : 0 ≤ mu := by
    unfold ShortPrimeIntervalMellin18.mu ShortPrimeIntervalWeight18.derivativeRatio
    positivity
  let B0 : ℝ := 1/(2*(10 : ℝ)^10*T^18)+1/(2*H^18)
  have hb : 1/(2*Real.sqrt X*T^18)+1/(2*H^18) ≤ (100/99 : ℝ)*B0 := by
    calc
      _ ≤ 1/(2*(9900000000 : ℝ)*T^18)+1/(2*H^18) := by gcongr
      _ ≤ _ := by norm_num [B0, T, H]
  have hc : c^19*mu/delta^18*B0 ≤ u/16 := by
    norm_num [B0, c, ShortPrimeIntervalMellin18.mu,
      ShortPrimeIntervalWeight18.derivativeRatio, delta, u, T, H]
  unfold highBound highFactor
  calc
    _ ≤ ((c+1)*c^19*mu*X/delta^18)*((100/99 : ℝ)*B0) := by
      gcongr
      · exact exp_u_le
      · exact delta_le
    _ = (c+1)*(100/99 : ℝ)*X*(c^19*mu/delta^18*B0) := by ring
    _ ≤ (c+1)*(100/99 : ℝ)*X*(u/16) := by gcongr
    _ ≤ (13/100 : ℝ)*u*X := by
      have hn : (c+1)*(100/99 : ℝ)/16 ≤ (13/100 : ℝ) := by norm_num [c]
      nlinarith only [mul_le_mul_of_nonneg_right hn (show 0 ≤ u*X by positivity)]

theorem paired_remainder_budget (X : ℝ) (hX : (99/100 : ℝ)*10^20 ≤ X) :
    2*bound X delta ≤ (5/100 : ℝ)*u*X := by
  have hX0 : 0 < X := by norm_num at hX; linarith
  have hs := sqrt_X_ge X hX
  have hs0 : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hp : (99/100 : ℝ)^2*10^30 ≤ X*Real.sqrt X := by
    have hm := mul_le_mul hX hs (by norm_num : (0 : ℝ) ≤ 9900000000) hX0.le
    norm_num at hm ⊢
    exact hm
  unfold bound
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0 < Real.sqrt X*delta^2)).mpr
  calc
    _ ≤ 2*(32768*c^2) := by gcongr; exact delta_le
    _ ≤ (5/100 : ℝ)*u*((99/100 : ℝ)^2*10^30)*delta^2 := by norm_num [c, delta, u]
    _ ≤ (5/100 : ℝ)*u*(X*Real.sqrt X)*delta^2 := by gcongr
    _ = _ := by ring

theorem prime_power_budget (X : ℝ) (hX : (99/100 : ℝ)*10^20 ≤ X) :
    (13/400 : ℝ)*Real.sqrt (X+X*delta) ≤ (1/100 : ℝ)*u*X := by
  have hX0 : 0 ≤ X := by norm_num at hX; linarith
  have hs := sqrt_X_ge X hX
  rw [show X+X*delta = X*(1+delta) by ring, Real.sqrt_mul hX0, ← mul_assoc]
  calc
    _ ≤ (13/400 : ℝ)*Real.sqrt X*c :=
      mul_le_mul_of_nonneg_left sqrt_delta_le (by positivity)
    _ ≤ (1/100 : ℝ)*u*Real.sqrt X*9900000000 := by
      have hn : (13/400 : ℝ)*c ≤ (1/100 : ℝ)*u*9900000000 := by norm_num [c, u]
      nlinarith only [mul_le_mul_of_nonneg_right hn (Real.sqrt_nonneg X)]
    _ ≤ (1/100 : ℝ)*u*Real.sqrt X*Real.sqrt X := by gcongr
    _ = _ := by nlinarith only [Real.sq_sqrt hX0]

end ShortPrimeIntervalBudgets18


-- Inlined checked source: Solutions/ShortPrimeIntervalDifference18.lean

noncomputable section
namespace ShortPrimeIntervalDifference18
open DusartSmoothing
open ShortPrimeIntervalNormalizedFormula18 (meanPsi term remainder)
open ShortPrimeIntervalIncrementSeries18 (increment lowBound highBound)

theorem meanPsi_difference (X u delta : ℝ) (hX : 1 ≤ X) (hu : 0 ≤ u) (hd : 0 < delta) :
    meanPsi (X*Real.exp u) delta - meanPsi X delta =
      (((Real.exp u-1)*X*(1+delta/2) : ℝ) : ℂ) -
        (∑' rho : NontrivialZetaZero, increment X u delta rho) +
        (remainder (X*Real.exp u) delta-remainder X delta) := by
  have he : 1 ≤ Real.exp u := Real.one_le_exp hu
  have hXe : 1 ≤ X*Real.exp u := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr he)]
  have hs1 := ShortPrimeIntervalNormalizedFormula18.term_summable (X*Real.exp u) delta hXe hd
  have hs0 := ShortPrimeIntervalNormalizedFormula18.term_summable X delta hX hd
  have hsum : (∑' rho : NontrivialZetaZero, increment X u delta rho) =
      (∑' rho : NontrivialZetaZero, term (X*Real.exp u) delta rho) -
        (∑' rho : NontrivialZetaZero, term X delta rho) := by
    rw [← hs1.tsum_sub hs0]
    apply tsum_congr
    intro rho
    unfold increment term
    rw [← ShortPrimeIntervalIncrement18.kernel_difference X u delta (by linarith) rho.val]
    ring
  rw [hsum, ShortPrimeIntervalNormalizedFormula18.normalized_formula _ _ hXe hd,
    ShortPrimeIntervalNormalizedFormula18.normalized_formula _ _ hX hd]
  push_cast
  ring

theorem meanPsi_difference_lower (X u delta T H N : ℝ)
    (hX : 1 ≤ X) (hu : 0 ≤ u) (hd : 0 < delta)
    (hT : (10 : ℝ)^8 ≤ T) (hTH : T ≤ H) (hlog : Real.log H ≤ 22)
    (hRH : ∀ rho : ℂ, RvM.IsNontrivialZero rho → |rho.im| ≤ H → rho.re = 1/2)
    (hN : (∑ rho ∈ ShortPrimeIntervalLowZeros18.lowZeros T,
      (RvM.zeroMult rho.val : ℝ)) ≤ N) :
    u*X - (lowBound X u delta N+highBound X u delta T H) -
        (‖remainder (X*Real.exp u) delta‖+‖remainder X delta‖) ≤
      (meanPsi (X*Real.exp u) delta-meanPsi X delta).re := by
  have hs := ShortPrimeIntervalIncrementSeries18.increment_norm_summable_bound
    X u delta T H N hX hu hd hT hTH hlog hRH hN
  have hmain : u*X ≤ (Real.exp u-1)*X*(1+delta/2) := by
    have he := Real.add_one_le_exp u
    have h1 : u*X ≤ (Real.exp u-1)*X := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h2 : 1 ≤ 1+delta/2 := by linarith
    exact h1.trans (le_mul_of_one_le_right (mul_nonneg (sub_nonneg.mpr (Real.one_le_exp hu)) (by linarith) : 0 ≤ (Real.exp u-1)*X) h2)
  have hr := norm_sub_le (remainder (X*Real.exp u) delta) (remainder X delta)
  have hz := Complex.re_le_norm (∑' rho : NontrivialZetaZero, increment X u delta rho)
  have hre := (abs_le.mp (Complex.abs_re_le_norm
    (remainder (X*Real.exp u) delta-remainder X delta))).1
  simp only [Complex.sub_re] at hre
  rw [meanPsi_difference X u delta hX hu hd]
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re]
  linarith only [hmain, hs.2, hr, hz, hre]

end ShortPrimeIntervalDifference18


-- Inlined checked source: Solutions/ShortPrimeIntervalWeightedPrime.lean

noncomputable section
open MeasureTheory
namespace ShortPrimeIntervalWeightedPrime

/-- A strict increase of theta supplies a prime, including endpoint conventions. -/
theorem prime_of_theta_lt (x y : ℝ) (hy0 : 0 ≤ y) (hyx : y ≤ x)
    (h : Chebyshev.theta y < Chebyshev.theta x) :
    ∃ p : ℕ, p.Prime ∧ y < (p : ℝ) ∧ (p : ℝ) ≤ x := by
  classical
  by_contra hex
  have hnone : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → (p : ℝ) ≤ y := by
    intro p hp hpx
    by_contra! hpy
    exact hex ⟨p, hp, hpy, hpx⟩
  have hx0 : 0 ≤ x := le_trans hy0 hyx
  have hsets : Nat.primesLE ⌊x⌋₊ = Nat.primesLE ⌊y⌋₊ := by
    ext p
    rw [Nat.mem_primesLE, Nat.mem_primesLE]
    constructor
    · rintro ⟨hpx, hp⟩
      exact ⟨Nat.le_floor (hnone p hp ((Nat.le_floor_iff hx0).mp hpx)), hp⟩
    · rintro ⟨hpy, hp⟩
      exact ⟨le_trans hpy (Nat.floor_le_floor hyx), hp⟩
  rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE, hsets] at h
  exact (lt_irrefl _) h

def f (t : ℝ) : ℝ := (4*t*(1-t))^18

theorem f_nonneg (t : ℝ) : 0 ≤ f t := by unfold f; positivity

theorem f_continuous : Continuous f := by unfold f; fun_prop

theorem prime_of_smoothed_psi (lo hi : ℝ → ℝ) (hlo : Monotone lo) (hhi : Monotone hi)
    (hmin : (10 : ℝ)^18 ≤ lo 0)
    (hdom : ∀ t ∈ Set.Icc (0 : ℝ) 1, lo t ≤ hi t)
    (hroot : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (hi t) ≤ (10001/10000 : ℝ)*Real.sqrt (lo t))
    (hpsi : (13/400 : ℝ)*Real.sqrt (lo 1)*(∫ t in (0 : ℝ)..1, f t) <
      ∫ t in (0 : ℝ)..1, f t*(Chebyshev.psi (hi t)-Chebyshev.psi (lo t))) :
    ∃ p : ℕ, p.Prime ∧ lo 0 < (p : ℝ) ∧ (p : ℝ) ≤ hi 1 := by
  let C : ℝ := (13/400 : ℝ)*Real.sqrt (lo 1)
  have hP (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      (Chebyshev.psi (hi t)-Chebyshev.theta (hi t))-
        (Chebyshev.psi (lo t)-Chebyshev.theta (lo t)) ≤ C := by
    have h := TaoFivePrimes.prime_power_correction_nearby (lo t) (hi t)
      (hmin.trans (hlo ht.1)) (hdom t ht) (hroot t ht)
    exact h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hlo ht.2)) (by norm_num))
  have hpsiHi := (Chebyshev.psi_mono.comp hhi).intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := 1)
  have hpsiLo := (Chebyshev.psi_mono.comp hlo).intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := 1)
  have hthetaHi := (Chebyshev.theta_mono.comp hhi).intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := 1)
  have hthetaLo := (Chebyshev.theta_mono.comp hlo).intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := 1)
  have hf := f_continuous
  have hiPsi := (hpsiHi.sub hpsiLo).continuousOn_mul hf.continuousOn
  have hiTheta := (hthetaHi.sub hthetaLo).continuousOn_mul hf.continuousOn
  simp only [Function.comp_apply] at hiPsi hiTheta
  have hiC : IntervalIntegrable (fun t : ℝ => C*f t) volume 0 1 :=
    (hf.const_mul C).intervalIntegrable 0 1
  have hle := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    hiPsi (hiTheta.add hiC) (fun t ht => by
      have h := mul_le_mul_of_nonneg_left (hP t ht) (f_nonneg t)
      nlinarith only [h])
  rw [intervalIntegral.integral_add hiTheta hiC, intervalIntegral.integral_const_mul] at hle
  have hpos : 0 < ∫ t in (0 : ℝ)..1, f t*(Chebyshev.theta (hi t)-Chebyshev.theta (lo t)) := by
    dsimp [C] at hle
    linarith only [hle, hpsi]
  have hbound := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    hiTheta ((hf.mul_const (Chebyshev.theta (hi 1)-Chebyshev.theta (lo 0))).intervalIntegrable 0 1)
    (fun t ht => by
      have h1 := Chebyshev.theta_mono (hhi ht.2)
      have h0 := Chebyshev.theta_mono (hlo ht.1)
      exact mul_le_mul_of_nonneg_left (by linarith) (f_nonneg t))
  rw [intervalIntegral.integral_mul_const] at hbound
  have hmass : 0 ≤ ∫ t in (0 : ℝ)..1, f t :=
    intervalIntegral.integral_nonneg (by norm_num) (fun t _ => f_nonneg t)
  have hgrow : Chebyshev.theta (lo 0) < Chebyshev.theta (hi 1) := by
    by_contra! h
    have hnon := mul_nonpos_of_nonneg_of_nonpos hmass (sub_nonpos.mpr h)
    linarith only [hpos, hbound, hnon]
  have hlo0 : 0 ≤ lo 0 := by norm_num at hmin; linarith
  have h01 : lo 0 ≤ hi 1 := (hlo (by norm_num : (0 : ℝ) ≤ 1)).trans (hdom 1 (by norm_num))
  exact prime_of_theta_lt (hi 1) (lo 0) hlo0 h01 hgrow

end ShortPrimeIntervalWeightedPrime


-- Inlined checked source: Solutions/ShortPrimeIntervalConditional18.lean

noncomputable section
open MeasureTheory
namespace ShortPrimeIntervalConditional18
open DusartSmoothing
open ShortPrimeIntervalBudgets18 (u delta T H c)
open ShortPrimeIntervalMellin18 (f mass mass_pos)
open ShortPrimeIntervalNormalizedFormula18 (meanPsi remainder)

theorem prime_from_base (X : ℝ) (hX : (99/100 : ℝ)*10^20 ≤ X)
    (hRH : ∀ rho : ℂ, RvM.IsNontrivialZero rho → |rho.im| ≤ H → rho.re = 1/2) :
    ∃ p : ℕ, p.Prime ∧ X < (p : ℝ) ∧ (p : ℝ) ≤ (X*Real.exp u)*(1+delta) := by
  have hX0 : 0 < X := by norm_num at hX; linarith
  have hX1 : 1 ≤ X := by norm_num at hX; linarith
  have hu : 0 ≤ u := by norm_num
  have hd : 0 < delta := by norm_num
  have hXe : X ≤ X*Real.exp u :=
    le_mul_of_one_le_right hX0.le (Real.one_le_exp hu)
  have hXe0 : 0 < X*Real.exp u := mul_pos hX0 (Real.exp_pos u)
  have hr0 := ShortPrimeIntervalRemainder18.norm_remainder_le X delta hX0 hd
  have hr1 := ShortPrimeIntervalRemainder18.norm_remainder_le (X*Real.exp u) delta hXe0 hd
  have hb : ShortPrimeIntervalRemainder18.bound (X*Real.exp u) delta ≤
      ShortPrimeIntervalRemainder18.bound X delta := by
    unfold ShortPrimeIntervalRemainder18.bound
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hXe) (sq_nonneg delta)
  have hrem : ‖remainder (X*Real.exp u) delta‖+‖remainder X delta‖ ≤ (5/100 : ℝ)*u*X := by
    calc
      _ ≤ ShortPrimeIntervalRemainder18.bound X delta+ShortPrimeIntervalRemainder18.bound X delta :=
        add_le_add (hr1.trans hb) hr0
      _ = 2*ShortPrimeIntervalRemainder18.bound X delta := by ring
      _ ≤ _ := ShortPrimeIntervalBudgets18.paired_remainder_budget X hX
  have hlow := ShortPrimeIntervalBudgets18.low_budget X hX
  have hhigh := ShortPrimeIntervalBudgets18.high_budget X hX
  have hpp := ShortPrimeIntervalBudgets18.prime_power_budget X hX
  have hmean := ShortPrimeIntervalDifference18.meanPsi_difference_lower X u delta T H 7854000000
    hX1 hu hd (by norm_num) (by norm_num) ShortPrimeIntervalBudgets18.log_H_le hRH
    ShortPrimeIntervalLowZeros18.total_low_count_fixed
  have hpos : (13/400 : ℝ)*Real.sqrt (X+X*delta) <
      (meanPsi (X*Real.exp u) delta-meanPsi X delta).re := by
    have hlower : (2/100 : ℝ)*u*X ≤
        (meanPsi (X*Real.exp u) delta-meanPsi X delta).re := by
      calc
        _ = u*X-((4/5 : ℝ)*u*X+(13/100 : ℝ)*u*X)-(5/100 : ℝ)*u*X := by ring
        _ ≤ u*X-(ShortPrimeIntervalIncrementSeries18.lowBound X u delta 7854000000+
            ShortPrimeIntervalIncrementSeries18.highBound X u delta T H)-
            (‖remainder (X*Real.exp u) delta‖+‖remainder X delta‖) := by gcongr
        _ ≤ _ := hmean
    exact hpp.trans_lt ((mul_lt_mul_of_pos_right
      (by norm_num : (1/100 : ℝ)*u < (2/100 : ℝ)*u) hX0).trans_le hlower)
  let lo : ℝ → ℝ := fun t => X+X*delta*t
  let hi : ℝ → ℝ := fun t => X*Real.exp u+(X*Real.exp u)*delta*t
  have hlo : Monotone lo := by
    intro a b hab
    dsimp only [lo]
    nlinarith only [mul_nonneg (mul_nonneg hX0.le hd.le) (sub_nonneg.mpr hab)]
  have hhi : Monotone hi := by
    intro a b hab
    dsimp only [hi]
    nlinarith only [mul_nonneg (mul_nonneg hXe0.le hd.le) (sub_nonneg.mpr hab)]
  have hf : Continuous f := by unfold f; fun_prop
  have hi0 := ((Chebyshev.psi_mono.comp hlo).intervalIntegrable
    (μ := volume) (a := (0 : ℝ)) (b := 1)).continuousOn_mul hf.continuousOn
  have hi1 := ((Chebyshev.psi_mono.comp hhi).intervalIntegrable
    (μ := volume) (a := (0 : ℝ)) (b := 1)).continuousOn_mul hf.continuousOn
  simp only [Function.comp_apply] at hi0 hi1
  have hIdiff : (∫ t in (0 : ℝ)..1, f t*(Chebyshev.psi (hi t)-Chebyshev.psi (lo t))) =
      (∫ t in (0 : ℝ)..1, f t*Chebyshev.psi (hi t)) -
        (∫ t in (0 : ℝ)..1, f t*Chebyshev.psi (lo t)) := by
    rw [← intervalIntegral.integral_sub hi1 hi0]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    ring
  have hreal : (meanPsi (X*Real.exp u) delta-meanPsi X delta).re =
      (∫ t in (0 : ℝ)..1, f t*(Chebyshev.psi (hi t)-Chebyshev.psi (lo t)))/mass := by
    rw [hIdiff, sub_div]
    simp only [meanPsi, ← Complex.ofReal_div, ← Complex.ofReal_sub, Complex.ofReal_re]
    rfl
  rw [hreal] at hpos
  have hmass := (lt_div_iff₀ mass_pos).mp hpos
  have he : Real.sqrt (Real.exp u) ≤ c := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by norm_num, ShortPrimeIntervalBudgets18.exp_u_le.trans (by norm_num [c])⟩
  have hex := ShortPrimeIntervalWeightedPrime.prime_of_smoothed_psi lo hi hlo hhi
    (by dsimp [lo]; norm_num at hX ⊢; linarith)
    (fun t ht => by
      have ht0 : 0 ≤ lo t := le_trans hX0.le (by simpa [lo] using hlo ht.1)
      have hscale : hi t = lo t*Real.exp u := by dsimp [lo, hi]; ring
      rw [hscale]
      exact le_mul_of_one_le_right ht0 (Real.one_le_exp hu))
    (fun t ht => by
      have ht0 : 0 ≤ lo t := le_trans hX0.le (by simpa [lo] using hlo ht.1)
      have hscale : hi t = lo t*Real.exp u := by dsimp [lo, hi]; ring
      rw [hscale, Real.sqrt_mul ht0]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg (lo t)))
    (by simpa only [lo, mul_one, ShortPrimeIntervalWeightedPrime.f, f, mass] using hmass)
  obtain ⟨p, hp, hplo, hphi⟩ := hex
  refine ⟨p, hp, ?_, ?_⟩
  · simpa [lo] using hplo
  · convert hphi using 1 <;> dsimp [hi] <;> ring

theorem prime_large_of_finiteRH (Y : ℝ) (hY : (10 : ℝ)^20 ≤ Y)
    (hRH : ∀ rho : ℂ, RvM.IsNontrivialZero rho → |rho.im| ≤ H → rho.re = 1/2) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ Y ∧ Y-p ≤ Y/(28000000 : ℝ) := by
  let D : ℝ := Real.exp u*(1+delta)
  let X : ℝ := Y/D
  have hD : 0 < D := by dsimp [D]; positivity
  have hY0 : 0 < Y := by norm_num at hY; linarith
  have hDc : D ≤ c*c := by
    dsimp [D]
    exact mul_le_mul ShortPrimeIntervalBudgets18.exp_u_le ShortPrimeIntervalBudgets18.delta_le
      (by norm_num) (by norm_num)
  have hXY : (99/100 : ℝ)*Y ≤ X := by
    dsimp [X]
    apply (le_div_iff₀ hD).mpr
    have hc : (99/100 : ℝ)*D ≤ 1 := by
      nlinarith only [mul_le_mul_of_nonneg_left hDc (by norm_num : (0 : ℝ) ≤ 99/100),
        show (99/100 : ℝ)*c*c ≤ 1 by norm_num [c]]
    nlinarith only [mul_le_mul_of_nonneg_right hc hY0.le]
  have hX : (99/100 : ℝ)*10^20 ≤ X :=
    (mul_le_mul_of_nonneg_left hY (by norm_num)).trans hXY
  obtain ⟨p, hp, hplo, hphi⟩ := prime_from_base X hX hRH
  have htop : (X*Real.exp u)*(1+delta) = Y := by dsimp [X, D]; field_simp <;> ring
  rw [htop] at hphi
  have he := Real.exp_bound_div_one_sub_of_interval (by norm_num : 0 ≤ u)
    (by norm_num : u < 1)
  have hwidthD : (1-1/(28000000 : ℝ))*D ≤ 1 := by
    have hd' : D ≤ (1/(1-u))*(1+delta) :=
      mul_le_mul_of_nonneg_right he (by norm_num)
    exact (mul_le_mul_of_nonneg_left hd' (by norm_num : (0 : ℝ) ≤ 1-1/28000000)).trans
      (by norm_num [delta, u])
  have hwidth : (1-1/(28000000 : ℝ))*Y ≤ X := by
    dsimp [X]
    apply (le_div_iff₀ hD).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hwidthD hY0.le]
  refine ⟨p, hp, hphi, ?_⟩
  linarith only [hwidth, hplo]

end ShortPrimeIntervalConditional18


-- Inlined checked source: Solutions/ShortPrimeIntervalConditionalFull.lean

noncomputable section
namespace ShortPrimeIntervalConditionalFull

theorem prime_interval_of_finiteRH
    (hRH : ∀ rho : ℂ, DusartSmoothing.RvM.IsNontrivialZero rho →
      |rho.im| ≤ (3290000000 : ℝ) → rho.re = 1/2)
    (x : ℝ) (hx : 1.1*10^10 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ x-p ≤ x/(2.8*10^7) := by
  by_cases hlarge : (10 : ℝ)^20 ≤ x
  · convert ShortPrimeIntervalConditional18.prime_large_of_finiteRH x hlarge hRH using 1 <;> norm_num
  · have hupper : x < (10 : ℝ)^20 := lt_of_not_ge hlarge
    have hx0 : 0 < x := by norm_num at hx; linarith
    obtain ⟨p, hp, hplo, hphi⟩ := RamareSaouter2003.prime_interval_finite_range x
      (by norm_num at hx ⊢; linarith) hupper
    refine ⟨p, hp, hphi, ?_⟩
    have hw : x*(1-1/(28314000 : ℝ)) ≥ x-x/(2.8*10^7) := by
      have hn : (1-1/(28000000 : ℝ)) ≤ 1-1/(28314000 : ℝ) := by norm_num
      nlinarith only [mul_le_mul_of_nonneg_left hn hx0.le]
    linarith only [hw, hplo]

end ShortPrimeIntervalConditionalFull


theorem solution
    (hRH : ∀ rho : ℂ, DusartSmoothing.RvM.IsNontrivialZero rho →
      |rho.im| ≤ (3290000000 : ℝ) → rho.re = 1/2)
    (x : ℝ) (hx : 1.1*10^10 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ x-p ≤ x/(2.8*10^7) :=
  ShortPrimeIntervalConditionalFull.prime_interval_of_finiteRH hRH x hx
