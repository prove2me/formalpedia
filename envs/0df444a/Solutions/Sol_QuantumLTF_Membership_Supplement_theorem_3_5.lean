-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.theorem_3_5
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-24T03:21:32.37587+00:00
-- url     : https://prove2.me/submissions/e9cb797e-723d-4b66-b9de-0e093ac6c996

import Mathlib
import Definitions.Def_QuantumLTF_Membership_sgn
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_Supplement_IsPOVM
import Definitions.Def_QuantumLTF_Membership_Supplement_QMemLearner
import Theorems.Thm_QuantumLTF_Membership_lemma_2_1

set_option autoImplicit false

open MeasureTheory Filter Polynomial QuantumLTF.Membership
open scoped Real Topology Nat ENNReal

namespace Aux_w_mq_lb

/-- Standard 1D Gaussian density `(√(2π))⁻¹ exp (-x² / 2)`. -/
noncomputable def phi (x : ℝ) : ℝ := ProbabilityTheory.gaussianPDFReal 0 1 x

lemma phi_def (x : ℝ) : phi x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)) := by
  simp [phi, ProbabilityTheory.gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one, neg_div]

lemma phi_zero : phi 0 = (Real.sqrt (2 * Real.pi))⁻¹ := by
  simp [phi_def]

lemma phi_neg (x : ℝ) : phi (-x) = phi x := by
  simp [phi_def]

lemma phi_pos (x : ℝ) : 0 < phi x :=
  ProbabilityTheory.gaussianPDFReal_pos 0 1 x one_ne_zero

lemma continuous_phi : Continuous phi := by
  have : phi = fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)) :=
    funext phi_def
  rw [this]
  fun_prop

lemma measurable_phi : Measurable phi := continuous_phi.measurable

lemma hasDerivAt_phi (x : ℝ) : HasDerivAt phi (-x * phi x) x := by
  have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-x) x := by
    have hpow := ((hasDerivAt_pow 2 x).div_const (2 : ℝ)).neg
    have hval : -(((2 : ℕ) : ℝ) * x ^ (2 - 1) / 2) = -x := by norm_num
    rw [hval] at hpow
    exact hpow
  have h2 := (h1.exp).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  have hfn : (fun y : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2 / 2))) = phi :=
    funext fun y => (phi_def y).symm
  rw [hfn] at h2
  refine h2.congr_deriv ?_
  rw [phi_def]; ring

/-- Unnormalized probabilists' Hermite polynomial evaluated on `ℝ`. -/
noncomputable def Hpoly (j : ℕ) (x : ℝ) : ℝ :=
  Polynomial.aeval x (Polynomial.hermite j)

lemma derivative_hermite (j : ℕ) :
    Polynomial.derivative (Polynomial.hermite (j + 1)) = C ((j + 1 : ℕ) : ℤ) * Polynomial.hermite j := by
  induction j with
  | zero =>
    rw [Polynomial.hermite_one, Polynomial.hermite_zero]
    simp
  | succ j ih =>
    rw [Polynomial.hermite_succ (j + 1), Polynomial.derivative_sub, Polynomial.derivative_mul,
      Polynomial.derivative_X, one_mul, ih, Polynomial.derivative_C_mul]
    have hmul : Polynomial.X * (C ((j + 1 : ℕ) : ℤ) * Polynomial.hermite j) -
        C ((j + 1 : ℕ) : ℤ) * Polynomial.derivative (Polynomial.hermite j) =
        C ((j + 1 : ℕ) : ℤ) * (Polynomial.X * Polynomial.hermite j -
          Polynomial.derivative (Polynomial.hermite j)) := by ring
    rw [← Polynomial.hermite_succ j] at hmul
    calc
      Polynomial.hermite (j + 1) + Polynomial.X * (C ((j + 1 : ℕ) : ℤ) * Polynomial.hermite j) -
          C ((j + 1 : ℕ) : ℤ) * Polynomial.derivative (Polynomial.hermite j)
          = Polynomial.hermite (j + 1) + (Polynomial.X * (C ((j + 1 : ℕ) : ℤ) * Polynomial.hermite j) -
              C ((j + 1 : ℕ) : ℤ) * Polynomial.derivative (Polynomial.hermite j)) := by ring
      _ = Polynomial.hermite (j + 1) + C ((j + 1 : ℕ) : ℤ) * Polynomial.hermite (j + 1) := by rw [hmul]
      _ = C (((j + 1 + 1 : ℕ) : ℤ)) * Polynomial.hermite (j + 1) := by
        have hC : C (((j + 1 + 1 : ℕ) : ℤ)) = 1 + C ((j + 1 : ℕ) : ℤ) := by
          push_cast; simp [map_add, map_one]; ring
        rw [hC]; ring

lemma hasDerivAt_Hpoly_succ (j : ℕ) (x : ℝ) :
    HasDerivAt (Hpoly (j + 1)) ((j + 1 : ℝ) * Hpoly j x) x := by
  let P : ℝ[X] := (Polynomial.hermite (j + 1)).map (algebraMap ℤ ℝ)
  have hP : HasDerivAt (fun y => P.eval y) (P.derivative.eval x) x := P.hasDerivAt x
  have h1 : (fun y => P.eval y) = Hpoly (j + 1) := by
    ext y; simp [P, Hpoly, Polynomial.aeval_def, Polynomial.eval_map]
  have h2 : P.derivative.eval x = (j + 1 : ℝ) * Hpoly j x := by
    dsimp [P]
    rw [Polynomial.derivative_map, derivative_hermite]
    simp [Hpoly, Polynomial.aeval_def, Polynomial.eval_map]
  rwa [h1, h2] at hP

lemma Hpoly_succ (j : ℕ) (x : ℝ) :
    Hpoly (j + 1) x = x * Hpoly j x - (j : ℝ) * (if j = 0 then 0 else Hpoly (j - 1) x) := by
  cases j with
  | zero =>
    simp [Hpoly, Polynomial.hermite_zero]
  | succ k =>
    have hderiv : Polynomial.aeval x (Polynomial.derivative (Polynomial.hermite (k + 1))) =
        ((k + 1 : ℕ) : ℝ) * Polynomial.aeval x (Polynomial.hermite k) := by
      rw [derivative_hermite k, map_mul]
      simp
    simp only [Hpoly, Polynomial.hermite_succ (k + 1), map_sub, map_mul, Polynomial.aeval_X]
    rw [hderiv]
    simp

lemma Hpoly_neg (j : ℕ) (x : ℝ) : Hpoly j (-x) = (-1 : ℝ) ^ j * Hpoly j x := by
  simp only [Hpoly, Polynomial.aeval_eq_sum_range]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hodd : Odd (j + k)
  · simp [Polynomial.coeff_hermite_of_odd_add hodd]
  · have heven : Even (j + k) := Nat.not_odd_iff_even.mp hodd
    have hpow : (-1 : ℝ) ^ k = (-1 : ℝ) ^ j := by
      have h1 : (-1 : ℝ) ^ (j + k) = 1 := heven.neg_one_pow
      rw [pow_add] at h1
      have hsq : (-1 : ℝ) ^ j * (-1 : ℝ) ^ j = 1 := by
        rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
      calc (-1 : ℝ) ^ k = ((-1 : ℝ) ^ j * (-1 : ℝ) ^ j) * (-1 : ℝ) ^ k := by rw [hsq, one_mul]
        _ = (-1 : ℝ) ^ j * ((-1 : ℝ) ^ j * (-1 : ℝ) ^ k) := mul_assoc _ _ _
        _ = (-1 : ℝ) ^ j := by rw [h1, mul_one]
    simp only [Algebra.smul_def, eq_intCast, neg_pow x k]
    rw [hpow]
    ring

/-- Normalized probabilists' Hermite function `h_j(x) = H_j(x) / √(j!)`. -/
noncomputable def h1D (j : ℕ) (x : ℝ) : ℝ :=
  (Real.sqrt (j.factorial : ℝ))⁻¹ * Hpoly j x

lemma continuous_h1D (j : ℕ) : Continuous (h1D j) := by
  have : h1D j = fun x =>
      (Real.sqrt (j.factorial : ℝ))⁻¹ * ((Polynomial.hermite j).map (algebraMap ℤ ℝ)).eval x := by
    ext x; simp [h1D, Hpoly, Polynomial.aeval_def, Polynomial.eval_map]
  rw [this]
  fun_prop

lemma h1D_zero_fn (x : ℝ) : h1D 0 x = 1 := by
  simp [h1D, Hpoly]

lemma h1D_neg (j : ℕ) (x : ℝ) : h1D j (-x) = (-1 : ℝ) ^ j * h1D j x := by
  simp only [h1D, Hpoly_neg]
  ring

lemma h1D_odd_zero (s : ℕ) : h1D (2 * s + 1) 0 = 0 := by
  have h := h1D_neg (2 * s + 1) 0
  simp only [neg_zero, pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul] at h
  linarith

noncomputable def h1D_deriv (j : ℕ) (x : ℝ) : ℝ :=
  if j = 0 then 0 else Real.sqrt (j : ℝ) * h1D (j - 1) x

lemma continuous_h1D_deriv (j : ℕ) : Continuous (h1D_deriv j) := by
  unfold h1D_deriv
  split_ifs
  · exact continuous_const
  · exact continuous_const.mul (continuous_h1D _)

lemma hasDerivAt_h1D (j : ℕ) (x : ℝ) : HasDerivAt (h1D j) (h1D_deriv j x) x := by
  cases j with
  | zero =>
    have : h1D 0 = fun _ => 1 := funext h1D_zero_fn
    rw [this, h1D_deriv]
    simp [hasDerivAt_const]
  | succ j =>
    have h := (hasDerivAt_Hpoly_succ j x).const_mul (Real.sqrt ((j + 1).factorial : ℝ))⁻¹
    have hfn : (fun y => (Real.sqrt ((j + 1).factorial : ℝ))⁻¹ * Hpoly (j + 1) y) = h1D (j + 1) := rfl
    rw [hfn] at h
    refine h.congr_deriv ?_
    simp only [h1D_deriv, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel, h1D, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hpos : (0 : ℝ) < j + 1 := by positivity
    rw [Real.sqrt_mul hpos.le, mul_inv]
    have hsq : (j + 1 : ℝ) * (Real.sqrt (j + 1 : ℝ))⁻¹ = Real.sqrt (j + 1 : ℝ) := by
      rw [eq_comm, eq_mul_inv_iff_mul_eq₀ (Real.sqrt_ne_zero'.mpr hpos), Real.mul_self_sqrt hpos.le]
    calc (Real.sqrt (j + 1 : ℝ))⁻¹ * (Real.sqrt (j.factorial : ℝ))⁻¹ * ((j + 1 : ℝ) * Hpoly j x)
        = ((j + 1 : ℝ) * (Real.sqrt (j + 1 : ℝ))⁻¹) * ((Real.sqrt (j.factorial : ℝ))⁻¹ * Hpoly j x) := by ring
      _ = Real.sqrt (j + 1 : ℝ) * ((Real.sqrt (j.factorial : ℝ))⁻¹ * Hpoly j x) := by rw [hsq]

lemma hasDerivAt_h1D_mul_phi (j : ℕ) (x : ℝ) :
    HasDerivAt (fun y => h1D j y * phi y) (-Real.sqrt (j + 1 : ℝ) * h1D (j + 1) x * phi x) x := by
  cases j with
  | zero =>
    have hfn : (fun y => h1D 0 y * phi y) = phi := by ext y; simp [h1D_zero_fn]
    rw [hfn]
    refine (hasDerivAt_phi x).congr_deriv ?_
    simp [h1D, Hpoly]
  | succ k =>
    have h1 := (hasDerivAt_h1D (k + 1) x).mul (hasDerivAt_phi x)
    refine h1.congr_deriv ?_
    have hrec := Hpoly_succ (k + 1) x
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel] at hrec
    have hk1 : (0 : ℝ) < k + 1 := by positivity
    have hk2 : (0 : ℝ) < k + 2 := by positivity
    have hfac : (Real.sqrt ((k + 2).factorial : ℝ))⁻¹ =
        (Real.sqrt (k + 2 : ℝ))⁻¹ * (Real.sqrt ((k + 1).factorial : ℝ))⁻¹ := by
      rw [Nat.factorial_succ (k + 1), Nat.cast_mul, Real.sqrt_mul (by positivity), mul_inv]
      push_cast; ring_nf
    have hfac2 : (Real.sqrt ((k + 1).factorial : ℝ))⁻¹ =
        (Real.sqrt (k + 1 : ℝ))⁻¹ * (Real.sqrt (k.factorial : ℝ))⁻¹ := by
      rw [Nat.factorial_succ k, Nat.cast_mul, Real.sqrt_mul (by positivity), mul_inv]
      push_cast; ring_nf
    have hsq : (k + 1 : ℝ) * (Real.sqrt (k + 1 : ℝ))⁻¹ = Real.sqrt (k + 1 : ℝ) := by
      rw [eq_comm, eq_mul_inv_iff_mul_eq₀ (Real.sqrt_ne_zero'.mpr hk1), Real.mul_self_sqrt hk1.le]
    have hsqrt_cancel : Real.sqrt (k + 2 : ℝ) * (Real.sqrt (k + 2 : ℝ))⁻¹ = 1 :=
      mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr hk2)
    simp only [h1D_deriv, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel, h1D]
    rw [show (k + 1 : ℕ) + 1 = k + 2 from rfl, hrec, hfac]
    push_cast
    calc Real.sqrt (k + 1 : ℝ) * ((Real.sqrt (k.factorial : ℝ))⁻¹ * Hpoly k x) * phi x +
          (Real.sqrt ((k + 1).factorial : ℝ))⁻¹ * Hpoly (k + 1) x * (-x * phi x)
        = (Real.sqrt (k + 1 : ℝ) * ((Real.sqrt (k.factorial : ℝ))⁻¹ * Hpoly k x) * phi x +
            ((Real.sqrt (k + 1 : ℝ))⁻¹ * (Real.sqrt (k.factorial : ℝ))⁻¹) * Hpoly (k + 1) x * (-x * phi x)) := by
            rw [hfac2]
      _ = ((k + 1 : ℝ) * (Real.sqrt (k + 1 : ℝ))⁻¹ * (Real.sqrt (k.factorial : ℝ))⁻¹ * Hpoly k x -
            x * (Real.sqrt (k + 1 : ℝ))⁻¹ * (Real.sqrt (k.factorial : ℝ))⁻¹ * Hpoly (k + 1) x) * phi x := by
            rw [hsq]; ring
      _ = ((k + 1 : ℝ) * (Real.sqrt ((k + 1).factorial : ℝ))⁻¹ * Hpoly k x -
            x * (Real.sqrt ((k + 1).factorial : ℝ))⁻¹ * Hpoly (k + 1) x) * phi x := by
            rw [hfac2]; ring
      _ = -((Real.sqrt (k + 2 : ℝ) * (Real.sqrt (k + 2 : ℝ))⁻¹) * (Real.sqrt ((k + 1).factorial : ℝ))⁻¹ *
            (x * Hpoly (k + 1) x - (k + 1 : ℝ) * Hpoly k x)) * phi x := by
            rw [hsqrt_cancel]; ring
      _ = _ := by ring

lemma hasDerivAt_h1D_deriv_mul_phi (j : ℕ) (x : ℝ) :
    HasDerivAt (fun y => phi y * h1D_deriv j y) (-(j : ℝ) * h1D j x * phi x) x := by
  cases j with
  | zero =>
    have hfn : (fun y => phi y * h1D_deriv 0 y) = fun _ => 0 := by ext y; simp [h1D_deriv]
    rw [hfn]
    simpa using hasDerivAt_const x (0 : ℝ)
  | succ k =>
    have hfn : (fun y => phi y * h1D_deriv (k + 1) y) =
        fun y => Real.sqrt (k + 1 : ℝ) * (h1D k y * phi y) := by
      ext y; simp [h1D_deriv]; ring
    rw [hfn]
    have h := (hasDerivAt_h1D_mul_phi k x).const_mul (Real.sqrt (k + 1 : ℝ))
    refine h.congr_deriv ?_
    have hk : (0 : ℝ) ≤ k + 1 := by positivity
    calc Real.sqrt (k + 1 : ℝ) * (-Real.sqrt (k + 1 : ℝ) * h1D (k + 1) x * phi x)
        = -((Real.sqrt (k + 1 : ℝ) * Real.sqrt (k + 1 : ℝ)) * h1D (k + 1) x * phi x) := by ring
      _ = -((k + 1 : ℝ) * h1D (k + 1) x * phi x) := by rw [Real.mul_self_sqrt hk]
      _ = -((k + 1 : ℕ) : ℝ) * h1D (k + 1) x * phi x := by push_cast; ring

lemma h1D_even_zero_abs_le (r : ℕ) :
    |h1D (2 * r) 0| ≤ ((2 * r + 1 : ℝ)) ^ (-1 / 4 : ℝ) := by
  have hcoeff : Hpoly (2 * r) 0 = (-1 : ℝ) ^ r * ((2 * r - 1)‼ : ℝ) := by
    have h0 := Polynomial.coeff_hermite_explicit r 0
    simp only [add_zero] at h0
    have hev : Hpoly (2 * r) 0 = ((Polynomial.hermite (2 * r)).coeff 0 : ℝ) := by
      simp [Hpoly, Polynomial.aeval_def, Polynomial.eval₂_at_zero]
    rw [hev, h0]
    simp [mul_comm]
  have hfac_eq : ∀ k : ℕ, (2 * k).factorial = (2 ^ k * k.factorial) * (2 * k - 1)‼ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hdf : (2 * (k + 1) - 1)‼ = (2 * k + 1) * (2 * k - 1)‼ := by
        cases k with
        | zero => simp
        | succ m =>
          have h2 : 2 * (m + 1 + 1) - 1 = (2 * (m + 1) - 1) + 2 := by omega
          rw [h2, Nat.doubleFactorial_add_two,
            show (2 * (m + 1) - 1 + 2) = 2 * (m + 1) + 1 by omega]
      have h1 : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
      rw [hdf, h1, Nat.factorial_succ, Nat.factorial_succ (2 * k), ih]
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      rw [hpow, Nat.factorial_succ]
      ring
  have hsq_eq : (h1D (2 * r) 0) ^ 2 = ((2 * r - 1)‼ : ℝ) / ((2 ^ r * r.factorial : ℕ) : ℝ) := by
    rw [h1D, hcoeff, mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _), hfac_eq r]
    have hneg1 : ((-1 : ℝ) ^ r) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have hdf_pos : (0 : ℝ) < (2 * r - 1)‼ := Nat.cast_pos.mpr (Nat.doubleFactorial_pos _)
    have hden_pos : (0 : ℝ) < (2 ^ r * r.factorial : ℕ) :=
      Nat.cast_pos.mpr (mul_pos (pow_pos (by norm_num) _) (Nat.factorial_pos _))
    rw [mul_pow, hneg1, one_mul, Nat.cast_mul]
    field_simp
  let a : ℕ → ℝ := fun k => ((2 * k - 1)‼ : ℝ) / ((2 ^ k * k.factorial : ℕ) : ℝ)
  have ha_step : ∀ k : ℕ, a (k + 1) = a k * (2 * k + 1 : ℝ) / (2 * k + 2 : ℝ) := by
    intro k
    simp only [a]
    have hdf : (2 * (k + 1) - 1)‼ = (2 * k + 1) * (2 * k - 1)‼ := by
      cases k with
      | zero => simp
      | succ m =>
        have h2 : 2 * (m + 1 + 1) - 1 = (2 * (m + 1) - 1) + 2 := by omega
        rw [h2, Nat.doubleFactorial_add_two,
          show (2 * (m + 1) - 1 + 2) = 2 * (m + 1) + 1 by omega]
    have hden_eq : 2 ^ (k + 1) * (k + 1).factorial = (2 * k + 2) * (2 ^ k * k.factorial) := by
      rw [pow_succ, Nat.factorial_succ]; ring
    rw [hdf, hden_eq]
    push_cast
    have hden1 : (0 : ℝ) < 2 ^ k * k.factorial := by positivity
    have hden2 : (0 : ℝ) < 2 * k + 2 := by positivity
    field_simp
  have hbound : ∀ k : ℕ, (2 * k + 1 : ℝ) * (a k) ^ 2 ≤ 1 := by
    intro k
    induction k with
    | zero => simp [a]
    | succ k ih =>
      rw [ha_step]
      have hden : (0 : ℝ) < 2 * k + 2 := by positivity
      have hnum : ((2 * (k + 1 : ℕ) + 1 : ℝ) * (2 * k + 1 : ℝ)) ≤ (2 * k + 2 : ℝ) ^ 2 := by
        push_cast; nlinarith
      have hratio : ((2 * (k + 1 : ℕ) + 1 : ℝ) * (2 * k + 1 : ℝ)) / (2 * k + 2 : ℝ) ^ 2 ≤ 1 :=
        (div_le_one (sq_pos_of_pos hden)).mpr hnum
      have halg : (2 * (k + 1 : ℕ) + 1 : ℝ) * (a k * (2 * k + 1 : ℝ) / (2 * k + 2 : ℝ)) ^ 2 =
          (((2 * (k + 1 : ℕ) + 1 : ℝ) * (2 * k + 1 : ℝ)) / (2 * k + 2 : ℝ) ^ 2) *
            ((2 * k + 1 : ℝ) * (a k) ^ 2) := by
        have hden' : (2 * (k : ℝ) + 2) ≠ 0 := hden.ne'
        field_simp
      rw [halg]
      have hnonneg : 0 ≤ (2 * (k : ℝ) + 1) * (a k) ^ 2 := by positivity
      calc (((2 * (k + 1 : ℕ) + 1 : ℝ) * (2 * k + 1 : ℝ)) / (2 * k + 2 : ℝ) ^ 2) *
            ((2 * k + 1 : ℝ) * (a k) ^ 2)
          ≤ 1 * 1 := mul_le_mul hratio ih hnonneg zero_le_one
        _ = 1 := one_mul 1
  have hpow4 : |h1D (2 * r) 0| ^ 4 ≤ 1 / (2 * r + 1 : ℝ) := by
    have h4 : |h1D (2 * r) 0| ^ 4 = ((h1D (2 * r) 0) ^ 2) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul', sq_abs]
    rw [h4, hsq_eq]
    have hpos : (0 : ℝ) < 2 * r + 1 := by positivity
    rw [le_div_iff₀ hpos]
    have hb := hbound r
    simpa [a, mul_comm] using hb
  have hrpos : (0 : ℝ) < 2 * r + 1 := by positivity
  rw [← Real.rpow_le_rpow_iff (abs_nonneg _) (Real.rpow_nonneg hrpos.le _) (by norm_num : (0 : ℝ) < 4)]
  calc |h1D (2 * r) 0| ^ (4 : ℝ) = |h1D (2 * r) 0| ^ (4 : ℕ) := Real.rpow_natCast _ 4
    _ ≤ 1 / (2 * r + 1 : ℝ) := hpow4
    _ = ((2 * r + 1 : ℝ) ^ (-1 / 4 : ℝ)) ^ (4 : ℝ) := by
        rw [← Real.rpow_mul hrpos.le, show (-1 / 4 : ℝ) * 4 = -1 by norm_num, Real.rpow_neg_one, one_div]

/-- Integrability of any polynomial against `phi`. -/
lemma integrable_pow_mul_phi (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k * phi x) volume := by
  have heven : ∀ m : ℕ, Integrable (fun x : ℝ => x ^ (2 * m) * phi x) volume := by
    intro m
    have h := (integrable_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
      (s := (2 * m : ℕ)) (by linarith [show (0 : ℝ) ≤ (2 * m : ℕ) by positivity])).const_mul
      (Real.sqrt (2 * Real.pi))⁻¹
    refine h.congr (ae_of_all _ fun x => ?_)
    simp only [Real.rpow_natCast, phi_def]
    ring
  have hdom : Integrable (fun x : ℝ => (1 + x ^ (2 * k)) * phi x) volume := by
    have h0 := heven 0
    have hk := heven k
    simp only [mul_zero, pow_zero, one_mul] at h0
    have hadd := h0.add hk
    refine hadd.congr (ae_of_all _ fun x => ?_)
    simp [add_mul]
  refine hdom.mono' ((continuous_pow k).mul continuous_phi).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (phi_pos x), abs_pow]
  have hx : |x| ^ k ≤ 1 + x ^ (2 * k) := by
    by_cases h1 : |x| ≤ 1
    · have : |x| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg x) h1
      have hx2 : 0 ≤ x ^ (2 * k) := by rw [mul_comm, pow_mul]; exact sq_nonneg _
      linarith
    · have h1' : 1 < |x| := lt_of_not_ge h1
      have hpow : |x| ^ k ≤ |x| ^ (2 * k) := pow_le_pow_right₀ h1'.le (by omega)
      have hsq : |x| ^ (2 * k) = x ^ (2 * k) := by
        rw [pow_mul, sq_abs, ← pow_mul]
      linarith
  exact mul_le_mul_of_nonneg_right hx (phi_pos x).le

lemma integrable_poly_mul_phi (P : Polynomial ℝ) :
    Integrable (fun x : ℝ => P.eval x * phi x) volume := by
  have hsum : (fun x : ℝ => P.eval x * phi x) =
      fun x => ∑ i ∈ P.support, (P.coeff i) * (x ^ i * phi x) := by
    ext x
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsum]
  exact integrable_finsetSum _ fun i _ => (integrable_pow_mul_phi i).const_mul _

lemma integrable_h1D_mul_h1D_mul_phi (j k : ℕ) :
    Integrable (fun x : ℝ => h1D j x * h1D k x * phi x) volume := by
  let P : Polynomial ℝ :=
    Polynomial.C ((Real.sqrt (j.factorial : ℝ))⁻¹ * (Real.sqrt (k.factorial : ℝ))⁻¹) *
      ((Polynomial.hermite j).map (algebraMap ℤ ℝ) * (Polynomial.hermite k).map (algebraMap ℤ ℝ))
  have hfn : (fun x : ℝ => h1D j x * h1D k x * phi x) = fun x => P.eval x * phi x := by
    ext x
    simp only [P, h1D, Hpoly, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.aeval_def, Polynomial.eval_map]
    ring
  rw [hfn]
  exact integrable_poly_mul_phi P

lemma integrable_h1D_mul_phi (j : ℕ) :
    Integrable (fun x : ℝ => h1D j x * phi x) volume := by
  simpa [h1D_zero_fn] using integrable_h1D_mul_h1D_mul_phi j 0

lemma tendsto_pow_mul_phi_atTop (k : ℕ) :
    Tendsto (fun x : ℝ => x ^ k * phi x) atTop (𝓝 0) := by
  have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  rw [mul_zero] at ht
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact mul_nonneg (pow_nonneg hx k) (phi_pos x).le
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    rw [phi_def]
    have hx0 : 0 ≤ x := by linarith
    have hexp : Real.exp (-(x ^ 2 / 2)) ≤ Real.exp (-x) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hmul : (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)) ≤
        (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    calc x ^ k * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)))
        ≤ x ^ k * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x)) :=
          mul_le_mul_of_nonneg_left hmul (pow_nonneg hx0 k)
      _ = (Real.sqrt (2 * Real.pi))⁻¹ * (x ^ k * Real.exp (-x)) := by ring

lemma tendsto_pow_mul_phi_atBot (k : ℕ) :
    Tendsto (fun x : ℝ => x ^ k * phi x) atBot (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => (-1 : ℝ) ^ k * ((-x) ^ k * phi (-x))) atBot (𝓝 ((-1 : ℝ) ^ k * 0)) :=
    ((tendsto_pow_mul_phi_atTop k).comp tendsto_neg_atBot_atTop).const_mul ((-1 : ℝ) ^ k)
  rw [mul_zero] at h1
  refine h1.congr fun x => ?_
  rw [phi_neg, neg_pow x k]
  calc (-1 : ℝ) ^ k * (((-1 : ℝ) ^ k * x ^ k) * phi x)
      = ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) * (x ^ k * phi x) := by ring
    _ = 1 * (x ^ k * phi x) := by rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    _ = x ^ k * phi x := one_mul _

lemma tendsto_poly_mul_phi_atTop (P : Polynomial ℝ) :
    Tendsto (fun x : ℝ => P.eval x * phi x) atTop (𝓝 0) := by
  have hsum : (fun x : ℝ => P.eval x * phi x) =
      fun x => ∑ i ∈ P.support, (P.coeff i) * (x ^ i * phi x) := by
    ext x
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  have hlim : Tendsto (fun x : ℝ => ∑ i ∈ P.support, (P.coeff i) * (x ^ i * phi x)) atTop
      (𝓝 (∑ i ∈ P.support, (P.coeff i) * 0)) :=
    tendsto_finsetSum _ fun i _ => (tendsto_pow_mul_phi_atTop i).const_mul _
  simpa using hlim

lemma tendsto_poly_mul_phi_atBot (P : Polynomial ℝ) :
    Tendsto (fun x : ℝ => P.eval x * phi x) atBot (𝓝 0) := by
  have hsum : (fun x : ℝ => P.eval x * phi x) =
      fun x => ∑ i ∈ P.support, (P.coeff i) * (x ^ i * phi x) := by
    ext x
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  have hlim : Tendsto (fun x : ℝ => ∑ i ∈ P.support, (P.coeff i) * (x ^ i * phi x)) atBot
      (𝓝 (∑ i ∈ P.support, (P.coeff i) * 0)) :=
    tendsto_finsetSum _ fun i _ => (tendsto_pow_mul_phi_atBot i).const_mul _
  simpa using hlim

lemma integral_poly_mul_h1D_succ (P : Polynomial ℝ) (m : ℕ) :
    ∫ x : ℝ, P.eval x * h1D (m + 1) x * phi x =
      (Real.sqrt (m + 1 : ℝ))⁻¹ * ∫ x : ℝ, P.derivative.eval x * h1D m x * phi x := by
  let F : ℝ → ℝ := fun x => P.eval x * (h1D m x * phi x)
  let F' : ℝ → ℝ := fun x =>
    P.derivative.eval x * h1D m x * phi x - Real.sqrt (m + 1 : ℝ) * (P.eval x * h1D (m + 1) x * phi x)
  have hderiv : ∀ x : ℝ, HasDerivAt F (F' x) x := by
    intro x
    have h := (P.hasDerivAt x).mul (hasDerivAt_h1D_mul_phi m x)
    refine h.congr_deriv ?_
    simp only [F']
    ring
  let Q : Polynomial ℝ :=
    P * (Polynomial.C (Real.sqrt (m.factorial : ℝ))⁻¹ * (Polynomial.hermite m).map (algebraMap ℤ ℝ))
  have hF_eq : F = fun x => Q.eval x * phi x := by
    ext x
    simp only [F, Q, h1D, Hpoly, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.aeval_def, Polynomial.eval_map]
    ring
  have h1_int : Integrable (fun x => P.derivative.eval x * h1D m x * phi x) volume := by
    have h := integrable_poly_mul_phi (P.derivative * (Polynomial.C (Real.sqrt (m.factorial : ℝ))⁻¹ *
      (Polynomial.hermite m).map (algebraMap ℤ ℝ)))
    refine h.congr (ae_of_all _ fun x => ?_)
    simp [h1D, Hpoly, Polynomial.aeval_def, Polynomial.eval_map, mul_assoc]
  have h2_int : Integrable (fun x => P.eval x * h1D (m + 1) x * phi x) volume := by
    have h := integrable_poly_mul_phi (P * (Polynomial.C (Real.sqrt ((m + 1).factorial : ℝ))⁻¹ *
      (Polynomial.hermite (m + 1)).map (algebraMap ℤ ℝ)))
    refine h.congr (ae_of_all _ fun x => ?_)
    simp [h1D, Hpoly, Polynomial.aeval_def, Polynomial.eval_map, mul_assoc]
  have hF'_int : Integrable F' volume := h1_int.sub (h2_int.const_mul _)
  have hint := integral_of_hasDerivAt_of_tendsto hderiv hF'_int
    (hF_eq ▸ tendsto_poly_mul_phi_atBot Q) (hF_eq ▸ tendsto_poly_mul_phi_atTop Q)
  rw [sub_self] at hint
  have hsub : ∫ x : ℝ, F' x =
      (∫ x : ℝ, P.derivative.eval x * h1D m x * phi x) -
      Real.sqrt (m + 1 : ℝ) * (∫ x : ℝ, P.eval x * h1D (m + 1) x * phi x) := by
    simp only [F']
    rw [integral_sub h1_int (h2_int.const_mul _), integral_const_mul]
  rw [hsub] at hint
  have hsqrt_ne : Real.sqrt (m + 1 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  have heq : Real.sqrt (m + 1 : ℝ) * (∫ x : ℝ, P.eval x * h1D (m + 1) x * phi x) =
      ∫ x : ℝ, P.derivative.eval x * h1D m x * phi x := by linarith
  rw [← heq, ← mul_assoc, inv_mul_cancel₀ hsqrt_ne, one_mul]

lemma h1D_orthonormal_aux (j k : ℕ) :
    ∫ x : ℝ, h1D j x * h1D k x * phi x = if j = k then 1 else 0 := by
  wlog hjk : j ≤ k generalizing j k
  · have hkj : k ≤ j := Nat.le_of_not_ge hjk
    have hsym : (fun x : ℝ => h1D j x * h1D k x * phi x) = fun x => h1D k x * h1D j x * phi x := by
      ext x; ring
    rw [hsym, this k j hkj]
    simp [eq_comm]
  induction k generalizing j with
  | zero =>
    have hj : j = 0 := by omega
    subst hj
    simp only [↓reduceIte, h1D_zero_fn, one_mul]
    exact ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 one_ne_zero
  | succ k ih =>
    let P : Polynomial ℝ :=
      Polynomial.C (Real.sqrt (j.factorial : ℝ))⁻¹ * (Polynomial.hermite j).map (algebraMap ℤ ℝ)
    have hP : ∀ x, h1D j x = P.eval x := by
      intro x; simp [P, h1D, Hpoly, Polynomial.aeval_def, Polynomial.eval_map]
    simp_rw [hP]
    rw [integral_poly_mul_h1D_succ P k]
    cases j with
    | zero =>
      have : P.derivative = 0 := by simp [P]
      simp [this]
    | succ m =>
      have hPderiv : ∀ x, P.derivative.eval x = Real.sqrt (m + 1 : ℝ) * h1D m x := by
        intro x
        simp only [P, Polynomial.derivative_C_mul, Polynomial.derivative_map,
          derivative_hermite m, Polynomial.map_mul, Polynomial.eval_mul, Polynomial.eval_C,
          h1D, Hpoly, Polynomial.aeval_def, Polynomial.eval_map]
        have hfac : (Real.sqrt ((m + 1).factorial : ℝ))⁻¹ =
            (Real.sqrt (m + 1 : ℝ))⁻¹ * (Real.sqrt (m.factorial : ℝ))⁻¹ := by
          rw [Nat.factorial_succ, Nat.cast_mul, Real.sqrt_mul (by positivity), mul_inv]
          push_cast; ring_nf
        have hp : (0 : ℝ) < m + 1 := by positivity
        have hsq : (m + 1 : ℝ) * (Real.sqrt (m + 1 : ℝ))⁻¹ = Real.sqrt (m + 1 : ℝ) := by
          rw [eq_comm, eq_mul_inv_iff_mul_eq₀ (Real.sqrt_ne_zero'.mpr hp), Real.mul_self_sqrt hp.le]
        rw [hfac, Polynomial.eval₂_C]
        simp only [eq_intCast, Int.cast_natCast]
        push_cast
        calc (Real.sqrt (m + 1 : ℝ))⁻¹ * (Real.sqrt (m.factorial : ℝ))⁻¹ *
              ((m + 1 : ℝ) * Polynomial.eval₂ (algebraMap ℤ ℝ) x (Polynomial.hermite m))
            = ((m + 1 : ℝ) * (Real.sqrt (m + 1 : ℝ))⁻¹) * ((Real.sqrt (m.factorial : ℝ))⁻¹ *
                Polynomial.eval₂ (algebraMap ℤ ℝ) x (Polynomial.hermite m)) := by ring
          _ = Real.sqrt (m + 1 : ℝ) * ((Real.sqrt (m.factorial : ℝ))⁻¹ *
                Polynomial.eval₂ (algebraMap ℤ ℝ) x (Polynomial.hermite m)) := by rw [hsq]
      simp_rw [hPderiv]
      have hmul : (fun x => Real.sqrt (m + 1 : ℝ) * h1D m x * h1D k x * phi x) =
          fun x => Real.sqrt (m + 1 : ℝ) * (h1D m x * h1D k x * phi x) := by ext x; ring
      rw [hmul, integral_const_mul]
      have hmle : m ≤ k := by omega
      rw [ih m hmle]
      rcases eq_or_lt_of_le hmle with rfl | hlt
      · simp only [↓reduceIte, mul_one]
        have hne : Real.sqrt (m + 1 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
        rw [inv_mul_cancel₀ hne]
      · have hne1 : m ≠ k := hlt.ne
        simp [hne1]

lemma h1D_orthonormal (j k : ℕ) :
    ∫ x : ℝ, h1D j x * h1D k x ∂(ProbabilityTheory.gaussianReal 0 1) =
      if j = k then 1 else 0 := by
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul one_ne_zero]
  have heq : (fun x : ℝ => ProbabilityTheory.gaussianPDFReal 0 1 x • (h1D j x * h1D k x)) =
      fun x => h1D j x * h1D k x * phi x := by
    ext x; simp [phi, smul_eq_mul]; ring
  rw [heq]
  exact h1D_orthonormal_aux j k

/-- Matrix of multiplication by `sgn` in the 1D Hermite basis. -/
noncomputable def M (j k : ℕ) : ℝ :=
  ∫ x : ℝ, (sgn x : ℝ) * h1D j x * h1D k x ∂(ProbabilityTheory.gaussianReal 0 1)

lemma M_symm (j k : ℕ) : M j k = M k j := by
  simp only [M]
  congr 1; ext x; ring

lemma M_eq_zero_of_even_add {j k : ℕ} (h : Even (j + k)) : M j k = 0 := by
  rw [M, ProbabilityTheory.integral_gaussianReal_eq_integral_smul one_ne_zero]
  have heq : (fun x : ℝ => ProbabilityTheory.gaussianPDFReal 0 1 x • ((sgn x : ℝ) * h1D j x * h1D k x)) =
      fun x => (sgn x : ℝ) * h1D j x * h1D k x * phi x := by
    ext x; simp [phi, smul_eq_mul]; ring
  rw [heq]
  have hneg : ∫ x : ℝ, (sgn (-x) : ℝ) * h1D j (-x) * h1D k (-x) * phi (-x) =
      ∫ x : ℝ, (sgn x : ℝ) * h1D j x * h1D k x * phi x :=
    integral_neg_eq_self (fun x => (sgn x : ℝ) * h1D j x * h1D k x * phi x) volume
  have hne0 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
    rw [ae_iff]; simp
  have hae : (fun x : ℝ => (sgn (-x) : ℝ) * h1D j (-x) * h1D k (-x) * phi (-x)) =ᵐ[volume]
      fun x : ℝ => -((sgn x : ℝ) * h1D j x * h1D k x * phi x) := by
    filter_upwards [hne0] with x hx
    have hsgn : (sgn (-x) : ℝ) = -(sgn x : ℝ) := by
      simp only [sgn]
      rcases lt_trichotomy x 0 with hlt | rfl | hgt
      · have h1 : ¬ (0 ≤ x) := not_le.mpr hlt
        have h2 : 0 ≤ -x := by linarith
        simp [h1, h2]
      · exact absurd rfl hx
      · have h1 : 0 ≤ x := hgt.le
        have h2 : ¬ (0 ≤ -x) := by linarith
        simp [h1, h2]
    rw [hsgn, h1D_neg, h1D_neg, phi_neg]
    have hpow : (-1 : ℝ) ^ j * (-1 : ℝ) ^ k = 1 := by
      rw [← pow_add]
      exact h.neg_one_pow
    calc -(sgn x : ℝ) * ((-1 : ℝ) ^ j * h1D j x) * ((-1 : ℝ) ^ k * h1D k x) * phi x
        = -(((-1 : ℝ) ^ j * (-1 : ℝ) ^ k) * ((sgn x : ℝ) * h1D j x * h1D k x * phi x)) := by ring
      _ = -((sgn x : ℝ) * h1D j x * h1D k x * phi x) := by rw [hpow, one_mul]
  rw [integral_congr_ae hae, integral_neg] at hneg
  linarith

lemma M_even_odd (r s : ℕ) :
    M (2 * r) (2 * s + 1) =
      Real.sqrt (2 / Real.pi) * (Real.sqrt (2 * s + 1 : ℝ) * h1D (2 * r) 0 * h1D (2 * s) 0) /
        ((2 * s + 1 : ℝ) - (2 * r : ℝ)) := by
  let j := 2 * r
  let k := 2 * s + 1
  have hM : M j k = 2 * ∫ x in Set.Ioi (0 : ℝ), h1D j x * h1D k x * phi x := by
    rw [M, ProbabilityTheory.integral_gaussianReal_eq_integral_smul one_ne_zero]
    have heq : (fun x : ℝ => ProbabilityTheory.gaussianPDFReal 0 1 x • ((sgn x : ℝ) * h1D j x * h1D k x)) =
        fun x => (sgn x : ℝ) * h1D j x * h1D k x * phi x := by
      ext x; simp [phi, smul_eq_mul]; ring
    rw [heq]
    have hint : Integrable (fun x : ℝ => (sgn x : ℝ) * h1D j x * h1D k x * phi x) volume := by
      refine (integrable_h1D_mul_h1D_mul_phi j k).norm.mono' ?_ (ae_of_all _ fun x => ?_)
      · have hsgn_meas : Measurable (fun x : ℝ => (sgn x : ℝ)) :=
          measurable_from_top.comp (Measurable.ite measurableSet_Ici measurable_const measurable_const)
        have hmeas : Measurable (fun x : ℝ => (sgn x : ℝ) * h1D j x * h1D k x * phi x) :=
          ((hsgn_meas.mul (continuous_h1D j).measurable).mul (continuous_h1D k).measurable).mul
            continuous_phi.measurable
        exact hmeas.aestronglyMeasurable
      · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
        have habs_sgn : |(sgn x : ℝ)| = 1 := by
          simp only [sgn]; split_ifs <;> norm_num
        rw [habs_sgn, one_mul, abs_mul, abs_mul]
    rw [← integral_add_compl measurableSet_Ioi hint]
    have hIoi : ∫ x in Set.Ioi (0 : ℝ), (sgn x : ℝ) * h1D j x * h1D k x * phi x =
        ∫ x in Set.Ioi (0 : ℝ), h1D j x * h1D k x * phi x := by
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      have : sgn x = 1 := if_pos (Set.mem_Ioi.mp hx).le
      simp [this]
    have hcompl : (Set.Ioi (0 : ℝ))ᶜ = Set.Iic 0 := Set.compl_Ioi
    have hIic : ∫ x in (Set.Ioi (0 : ℝ))ᶜ, (sgn x : ℝ) * h1D j x * h1D k x * phi x =
        ∫ x in Set.Ioi (0 : ℝ), h1D j x * h1D k x * phi x := by
      rw [hcompl, integral_Iic_eq_integral_Iio, ← integral_indicator measurableSet_Iio,
        ← integral_neg_eq_self]
      have hind : (fun x : ℝ => Set.indicator (Set.Iio 0)
            (fun y => (sgn y : ℝ) * h1D j y * h1D k y * phi y) (-x)) =
          Set.indicator (Set.Ioi 0) (fun x => h1D j x * h1D k x * phi x) := by
        ext x
        by_cases hx : 0 < x
        · have hxneg : -x ∈ Set.Iio (0 : ℝ) := Set.mem_Iio.mpr (by linarith)
          have hx' : x ∈ Set.Ioi (0 : ℝ) := hx
          rw [Set.indicator_of_mem hxneg, Set.indicator_of_mem hx']
          have hsgn : sgn (-x) = -1 := if_neg (by linarith)
          simp only [hsgn, Int.cast_neg, Int.cast_one, h1D_neg, phi_neg]
          have hjpow : (-1 : ℝ) ^ j = 1 := (even_two_mul r).neg_one_pow
          have hkpow : (-1 : ℝ) ^ k = -1 := Odd.neg_one_pow ⟨s, rfl⟩
          rw [hjpow, hkpow]
          ring
        · have hxneg : -x ∉ Set.Iio (0 : ℝ) := by simp only [Set.mem_Iio]; linarith
          have hx' : x ∉ Set.Ioi (0 : ℝ) := hx
          rw [Set.indicator_of_notMem hxneg, Set.indicator_of_notMem hx']
      rw [hind, integral_indicator measurableSet_Ioi]
    rw [hIoi, hIic, two_mul]
  let F : ℝ → ℝ := fun x => phi x * (h1D_deriv j x * h1D k x - h1D j x * h1D_deriv k x)
  have hF_deriv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt F (((k : ℝ) - j) * (h1D j x * h1D k x * phi x)) x := by
    intro x _
    have h1 := ((hasDerivAt_h1D_deriv_mul_phi j x).mul (hasDerivAt_h1D k x)).sub
      ((hasDerivAt_h1D j x).mul (hasDerivAt_h1D_deriv_mul_phi k x))
    have hF_eq : ((fun y => phi y * h1D_deriv j y) * h1D k - h1D j * fun y => phi y * h1D_deriv k y) = F := by
      ext y; simp [F]; ring
    rw [hF_eq] at h1
    refine h1.congr_deriv ?_
    ring
  have hF_cont : Continuous F :=
    continuous_phi.mul (((continuous_h1D_deriv j).mul (continuous_h1D k)).sub
      ((continuous_h1D j).mul (continuous_h1D_deriv k)))
  have hF_poly : ∃ Q : Polynomial ℝ, F = fun x => Q.eval x * phi x := by
    let Pj : Polynomial ℝ :=
      Polynomial.C (Real.sqrt (j.factorial : ℝ))⁻¹ * (Polynomial.hermite j).map (algebraMap ℤ ℝ)
    let Pk : Polynomial ℝ :=
      Polynomial.C (Real.sqrt (k.factorial : ℝ))⁻¹ * (Polynomial.hermite k).map (algebraMap ℤ ℝ)
    let Pjd : Polynomial ℝ :=
      if j = 0 then 0 else Polynomial.C (Real.sqrt (j : ℝ) * (Real.sqrt ((j - 1).factorial : ℝ))⁻¹) *
        (Polynomial.hermite (j - 1)).map (algebraMap ℤ ℝ)
    let Pkd : Polynomial ℝ :=
      if k = 0 then 0 else Polynomial.C (Real.sqrt (k : ℝ) * (Real.sqrt ((k - 1).factorial : ℝ))⁻¹) *
        (Polynomial.hermite (k - 1)).map (algebraMap ℤ ℝ)
    refine ⟨Pjd * Pk - Pj * Pkd, ?_⟩
    ext x
    have hPj : Pj.eval x = h1D j x := by
      simp [Pj, h1D, Hpoly, Polynomial.aeval_def, Polynomial.eval_map]
    have hPk : Pk.eval x = h1D k x := by
      simp [Pk, h1D, Hpoly, Polynomial.aeval_def, Polynomial.eval_map]
    have hPjd : Pjd.eval x = h1D_deriv j x := by
      simp only [Pjd, h1D_deriv]
      split_ifs <;> simp [h1D, Hpoly, Polynomial.aeval_def, Polynomial.eval_map, mul_assoc]
    have hPkd : Pkd.eval x = h1D_deriv k x := by
      simp only [Pkd, h1D_deriv]
      split_ifs <;> simp [h1D, Hpoly, Polynomial.aeval_def, Polynomial.eval_map, mul_assoc]
    simp only [F, Polynomial.eval_sub, Polynomial.eval_mul, hPj, hPk, hPjd, hPkd]
    ring
  obtain ⟨Q, hQ⟩ := hF_poly
  have hF_tendsto : Tendsto F atTop (𝓝 0) := hQ ▸ tendsto_poly_mul_phi_atTop Q
  have hF'_int : IntegrableOn (fun x => ((k : ℝ) - j) * (h1D j x * h1D k x * phi x)) (Set.Ioi 0) volume :=
    ((integrable_h1D_mul_h1D_mul_phi j k).const_mul ((k : ℝ) - j)).integrableOn
  have hint_eq := integral_Ioi_of_hasDerivAt_of_tendsto hF_cont.continuousWithinAt hF_deriv hF'_int hF_tendsto
  rw [integral_const_mul, zero_sub] at hint_eq
  have hF0 : F 0 = -phi 0 * h1D (2 * r) 0 * Real.sqrt (2 * s + 1 : ℝ) * h1D (2 * s) 0 := by
    have hk_odd : h1D (2 * s + 1) 0 = 0 := h1D_odd_zero s
    have hkd : h1D_deriv (2 * s + 1) 0 = Real.sqrt (2 * s + 1 : ℝ) * h1D (2 * s) 0 := by
      simp [h1D_deriv]
    simp only [F, j, k, hk_odd, mul_zero, zero_sub, hkd]
    ring
  rw [hF0] at hint_eq
  have hne : (k : ℝ) - j ≠ 0 := by
    have hne' : (2 * s + 1 : ℤ) ≠ 2 * r := by omega
    intro hzero
    dsimp [j, k] at hzero
    apply hne'
    have hzero' : (2 * (s : ℝ) + 1) = 2 * (r : ℝ) := by push_cast at hzero; linarith
    exact_mod_cast hzero'
  have hint_Ioi : ∫ x in Set.Ioi (0 : ℝ), h1D j x * h1D k x * phi x =
      (phi 0 * h1D (2 * r) 0 * Real.sqrt (2 * s + 1 : ℝ) * h1D (2 * s) 0) / ((2 * s + 1 : ℝ) - (2 * r : ℝ)) := by
    have h1 : ((k : ℝ) - j) * ∫ x in Set.Ioi (0 : ℝ), h1D j x * h1D k x * phi x =
        phi 0 * h1D (2 * r) 0 * Real.sqrt (2 * s + 1 : ℝ) * h1D (2 * s) 0 := by
      linarith
    rw [eq_div_iff (by simpa [j, k] using hne)]
    calc (∫ x in Set.Ioi (0 : ℝ), h1D j x * h1D k x * phi x) * ((2 * s + 1 : ℝ) - (2 * r : ℝ))
        = ((k : ℝ) - j) * ∫ x in Set.Ioi (0 : ℝ), h1D j x * h1D k x * phi x := by
            simp only [j, k]; push_cast; ring
      _ = phi 0 * h1D (2 * r) 0 * Real.sqrt (2 * s + 1 : ℝ) * h1D (2 * s) 0 := h1
  rw [hM, hint_Ioi]
  have h2phi : 2 * phi 0 = Real.sqrt (2 / Real.pi) := by
    rw [phi_zero, Real.sqrt_div (by positivity)]
    have hpi : 0 < Real.pi := Real.pi_pos
    have h2pi : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
      Real.sqrt_mul (by norm_num) Real.pi
    rw [h2pi]
    have h2ne : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
    have hpine : Real.sqrt Real.pi ≠ 0 := Real.sqrt_ne_zero'.mpr hpi
    have hsq2 : (2 : ℝ) = Real.sqrt 2 ^ 2 := (Real.sq_sqrt (by norm_num)).symm
    field_simp
    exact hsq2
  calc 2 * ((phi 0 * h1D (2 * r) 0 * Real.sqrt (2 * s + 1 : ℝ) * h1D (2 * s) 0) /
          ((2 * s + 1 : ℝ) - (2 * r : ℝ)))
      = ((2 * phi 0) * (Real.sqrt (2 * s + 1 : ℝ) * h1D (2 * r) 0 * h1D (2 * s) 0)) /
          ((2 * s + 1 : ℝ) - (2 * r : ℝ)) := by ring
    _ = _ := by rw [h2phi]

lemma M_abs_le {j k : ℕ} (hjk : j ≠ k) :
    |M j k| ≤ (max (j + 1 : ℝ) (k + 1) / min (j + 1 : ℝ) (k + 1)) ^ (1 / 4 : ℝ) / |(j : ℝ) - k| := by
  by_cases heven : Even (j + k)
  · rw [M_eq_zero_of_even_add heven, abs_zero]
    positivity
  have hodd : Odd (j + k) := Nat.not_even_iff_odd.mp heven
  have h2pi : Real.sqrt (2 / Real.pi) ≤ 1 := by
    rw [Real.sqrt_le_one]
    rw [div_le_one Real.pi_pos]
    linarith [Real.pi_gt_three]
  have hhelper : ∀ r s : ℕ,
      |M (2 * r) (2 * s + 1)| ≤
        (max ((2 * r : ℝ) + 1) ((2 * s + 1 : ℝ) + 1) / min ((2 * r : ℝ) + 1) ((2 * s + 1 : ℝ) + 1)) ^ (1 / 4 : ℝ) /
          |((2 * r : ℝ)) - (2 * s + 1 : ℝ)| := by
    intro r s
    rw [M_even_odd r s, abs_div, abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (Real.sqrt_nonneg _)]
    have hr := h1D_even_zero_abs_le r
    have hs := h1D_even_zero_abs_le s
    have hrpos : (0 : ℝ) < 2 * r + 1 := by positivity
    have hspos : (0 : ℝ) < 2 * s + 1 := by positivity
    have hsqrt_s : Real.sqrt (2 * s + 1 : ℝ) = (2 * s + 1 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
    have hnum : Real.sqrt (2 / Real.pi) * (Real.sqrt (2 * s + 1 : ℝ) * |h1D (2 * r) 0| * |h1D (2 * s) 0|) ≤
        ((2 * s + 1 : ℝ) / (2 * r + 1 : ℝ)) ^ (1 / 4 : ℝ) := by
      calc Real.sqrt (2 / Real.pi) * (Real.sqrt (2 * s + 1 : ℝ) * |h1D (2 * r) 0| * |h1D (2 * s) 0|)
          ≤ 1 * (Real.sqrt (2 * s + 1 : ℝ) * ((2 * r + 1 : ℝ) ^ (-1 / 4 : ℝ)) *
              ((2 * s + 1 : ℝ) ^ (-1 / 4 : ℝ))) := by gcongr
        _ = ((2 * s + 1 : ℝ) ^ (1 / 2 : ℝ) * (2 * s + 1 : ℝ) ^ (-1 / 4 : ℝ)) *
              (2 * r + 1 : ℝ) ^ (-1 / 4 : ℝ) := by rw [one_mul, hsqrt_s]; ring
        _ = (2 * s + 1 : ℝ) ^ (1 / 4 : ℝ) * (2 * r + 1 : ℝ) ^ (-1 / 4 : ℝ) := by
            rw [← Real.rpow_add hspos, show (1 / 2 : ℝ) + (-1 / 4 : ℝ) = 1 / 4 by norm_num]
        _ = (2 * s + 1 : ℝ) ^ (1 / 4 : ℝ) / (2 * r + 1 : ℝ) ^ (1 / 4 : ℝ) := by
            rw [show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by norm_num, Real.rpow_neg hrpos.le, ← div_eq_mul_inv]
        _ = ((2 * s + 1 : ℝ) / (2 * r + 1 : ℝ)) ^ (1 / 4 : ℝ) := by
            rw [← Real.div_rpow hspos.le hrpos.le]
    have hratio : (2 * s + 1 : ℝ) / (2 * r + 1 : ℝ) ≤
        max ((2 * r : ℝ) + 1) ((2 * s + 1 : ℝ) + 1) / min ((2 * r : ℝ) + 1) ((2 * s + 1 : ℝ) + 1) := by
      have ha : (0 : ℝ) < (2 * r : ℝ) + 1 := by positivity
      have hb : (0 : ℝ) < (2 * s + 1 : ℝ) + 1 := by positivity
      have hmin_pos : 0 < min ((2 * r : ℝ) + 1) ((2 * s + 1 : ℝ) + 1) := lt_min ha hb
      rw [div_le_div_iff₀ ha hmin_pos]
      have hle1 : (2 * s + 1 : ℝ) ≤ max ((2 * r : ℝ) + 1) ((2 * s + 1 : ℝ) + 1) :=
        le_trans (by linarith) (le_max_right _ _)
      have hle2 : min ((2 * r : ℝ) + 1) ((2 * s + 1 : ℝ) + 1) ≤ (2 * r : ℝ) + 1 := min_le_left _ _
      exact mul_le_mul hle1 hle2 hmin_pos.le (by positivity)
    have hnum2 : ((2 * s + 1 : ℝ) / (2 * r + 1 : ℝ)) ^ (1 / 4 : ℝ) ≤
        (max ((2 * r : ℝ) + 1) ((2 * s + 1 : ℝ) + 1) / min ((2 * r : ℝ) + 1) ((2 * s + 1 : ℝ) + 1)) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hratio (by norm_num)
    have hden : |(2 * s + 1 : ℝ) - (2 * r : ℝ)| = |((2 * r : ℝ)) - (2 * s + 1 : ℝ)| := abs_sub_comm _ _
    rw [hden]
    exact div_le_div_of_nonneg_right (hnum.trans hnum2) (abs_nonneg _)
  rcases Nat.even_or_odd j with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · rcases Nat.even_or_odd k with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · exfalso; apply heven; exact ⟨r + s, by ring⟩
    · have h := hhelper r s
      simpa [two_mul] using h
  · rcases Nat.even_or_odd k with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · rw [M_symm]
      have h := hhelper s r
      simpa [two_mul, max_comm, min_comm, abs_sub_comm] using h
    · exfalso; apply heven; exact ⟨r + s + 1, by ring⟩

/-! ### Weighted Schur Test for `K m` -/

noncomputable def Kmat (m j k : ℕ) : ℝ :=
  ((((j + m + 1 : ℝ) / (k + m + 1 : ℝ)) ^ (1 / 8 : ℝ)) - 1) * M j k

lemma rpow_eighth_sub_one_le (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    |(a / b) ^ (1 / 8 : ℝ) - 1| ≤ |a - b| / b := by
  set x : ℝ := (a / b) ^ (1 / 8 : ℝ)
  have hx_pos : 0 < x := Real.rpow_pos_of_pos (div_pos ha hb) _
  have hx8 : x ^ 8 = a / b := by
    rw [← Real.rpow_natCast x 8]
    dsimp [x]
    rw [← Real.rpow_mul (div_pos ha hb).le]
    norm_num
  have hfac : x ^ 8 - 1 = (x - 1) * (∑ i ∈ Finset.range 8, x ^ i) := by
    have := mul_geom_sum x 8
    linarith
  have hsum_ge : (1 : ℝ) ≤ ∑ i ∈ Finset.range 8, x ^ i := by
    have hmem : (0 : ℕ) ∈ Finset.range 8 := by simp
    calc (1 : ℝ) = x ^ 0 := (pow_zero x).symm
      _ ≤ ∑ i ∈ Finset.range 8, x ^ i :=
          Finset.single_le_sum (fun i _ => pow_nonneg hx_pos.le i) hmem
  have hdiv : |x - 1| = |x ^ 8 - 1| / |∑ i ∈ Finset.range 8, x ^ i| := by
    rw [hfac, abs_mul]
    have hpos_sum : 0 < |∑ i ∈ Finset.range 8, x ^ i| := abs_pos.mpr (by linarith)
    field_simp
  have hsum_pos : 0 < ∑ i ∈ Finset.range 8, x ^ i := by linarith
  rw [hdiv, abs_of_pos hsum_pos]
  calc |x ^ 8 - 1| / ∑ i ∈ Finset.range 8, x ^ i
      ≤ |x ^ 8 - 1| / 1 := div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hsum_ge
    _ = |a / b - 1| := by rw [div_one, hx8]
    _ = |a - b| / b := by
        rw [show a / b - 1 = (a - b) / b by field_simp, abs_div, abs_of_pos hb]

lemma shift_ratio_sub_one_le (a b m : ℝ) (ha : 0 < a) (hb : 0 < b) (hm : 0 ≤ m) :
    |((a + m) / (b + m)) ^ (1 / 8 : ℝ) - 1| ≤ |(a / b) ^ (1 / 8 : ℝ) - 1| := by
  have hbm : 0 < b + m := by linarith
  have ham : 0 < a + m := by linarith
  rcases le_total a b with hab | hba
  · have h1 : a / b ≤ (a + m) / (b + m) := by
      rw [div_le_div_iff₀ hb hbm]
      nlinarith
    have h2 : (a + m) / (b + m) ≤ 1 := (div_le_one hbm).mpr (by linarith)
    have h3 : (a / b) ^ (1 / 8 : ℝ) ≤ ((a + m) / (b + m)) ^ (1 / 8 : ℝ) :=
      Real.rpow_le_rpow (div_pos ha hb).le h1 (by norm_num)
    have h4 : ((a + m) / (b + m)) ^ (1 / 8 : ℝ) ≤ 1 :=
      Real.rpow_le_one (div_pos ham hbm).le h2 (by norm_num)
    have h5 : (a / b) ^ (1 / 8 : ℝ) ≤ 1 := h3.trans h4
    rw [abs_of_nonpos (sub_nonpos.mpr h4), abs_of_nonpos (sub_nonpos.mpr h5)]
    linarith
  · have h1 : 1 ≤ (a + m) / (b + m) := (one_le_div hbm).mpr (by linarith)
    have h2 : (a + m) / (b + m) ≤ a / b := by
      rw [div_le_div_iff₀ hbm hb]
      nlinarith
    have h3 : (1 : ℝ) ≤ ((a + m) / (b + m)) ^ (1 / 8 : ℝ) :=
      Real.one_le_rpow h1 (by norm_num)
    have h4 : ((a + m) / (b + m)) ^ (1 / 8 : ℝ) ≤ (a / b) ^ (1 / 8 : ℝ) :=
      Real.rpow_le_rpow (div_pos ham hbm).le h2 (by norm_num)
    have h5 : (1 : ℝ) ≤ (a / b) ^ (1 / 8 : ℝ) := h3.trans h4
    rw [abs_of_nonneg (sub_nonneg.mpr h3), abs_of_nonneg (sub_nonneg.mpr h5)]
    linarith

lemma Kmat_abs_le (m j k : ℕ) :
    |Kmat m j k| ≤
      let a : ℝ := j + 1
      let b : ℝ := k + 1
      if j = k then 0
      else if 2 * b ≤ a then 2 * a ^ (-5 / 8 : ℝ) * b ^ (-3 / 8 : ℝ)
      else if 2 * a ≤ b then 2 * a ^ (-1 / 4 : ℝ) * b ^ (-3 / 4 : ℝ)
      else 4 * a⁻¹ := by
  dsimp only
  split_ifs with hjk h2b h2a
  · subst hjk
    have hev : Even (j + j) := ⟨j, by ring⟩
    simp [Kmat, M_eq_zero_of_even_add hev]
  · set a : ℝ := j + 1
    set b : ℝ := k + 1
    have ha : 0 < a := by positivity
    have hb : 0 < b := by positivity
    have hM := M_abs_le hjk
    have hshift := shift_ratio_sub_one_le a b (m : ℝ) ha hb (Nat.cast_nonneg m)
    have hdiff : |(a / b) ^ (1 / 8 : ℝ) - 1| ≤ (a / b) ^ (1 / 8 : ℝ) := by
      have hge : 1 ≤ a / b := (one_le_div hb).mpr (by linarith)
      have hge1 : 1 ≤ (a / b) ^ (1 / 8 : ℝ) := Real.one_le_rpow hge (by norm_num)
      rw [abs_of_nonneg (sub_nonneg.mpr hge1)]
      linarith
    have hmax : max a b = a := max_eq_left (by linarith)
    have hmin : min a b = b := min_eq_right (by linarith)
    have hgap : a / 2 ≤ |(j : ℝ) - k| := by
      have hjk' : (j : ℝ) - k = a - b := by simp [a, b]
      rw [hjk', abs_of_nonneg (by linarith)]
      linarith
    have hM' : |M j k| ≤ (a / b) ^ (1 / 4 : ℝ) * (2 / a) := by
      have h1 : (max a b / min a b) ^ (1 / 4 : ℝ) / |(j : ℝ) - k| ≤ (a / b) ^ (1 / 4 : ℝ) / (a / 2) := by
        rw [hmax, hmin]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hgap
      calc |M j k| ≤ (max a b / min a b) ^ (1 / 4 : ℝ) / |(j : ℝ) - k| := by simpa [a, b] using hM
        _ ≤ (a / b) ^ (1 / 4 : ℝ) / (a / 2) := h1
        _ = (a / b) ^ (1 / 4 : ℝ) * (2 / a) := by ring
    have hshift' : |((j + m + 1 : ℝ) / (k + m + 1 : ℝ)) ^ (1 / 8 : ℝ) - 1| ≤ (a / b) ^ (1 / 8 : ℝ) := by
      calc |((j + m + 1 : ℝ) / (k + m + 1 : ℝ)) ^ (1 / 8 : ℝ) - 1|
          = |((a + m) / (b + m)) ^ (1 / 8 : ℝ) - 1| := by simp [a, b, add_assoc, add_comm]
        _ ≤ |(a / b) ^ (1 / 8 : ℝ) - 1| := hshift
        _ ≤ (a / b) ^ (1 / 8 : ℝ) := hdiff
    rw [Kmat, abs_mul]
    calc |((j + m + 1 : ℝ) / (k + m + 1 : ℝ)) ^ (1 / 8 : ℝ) - 1| * |M j k|
        ≤ (a / b) ^ (1 / 8 : ℝ) * ((a / b) ^ (1 / 4 : ℝ) * (2 / a)) :=
          mul_le_mul hshift' hM' (abs_nonneg _) (by positivity)
      _ = 2 * ((a ^ (1 / 8 : ℝ) * a ^ (1 / 4 : ℝ) * a⁻¹) * (b ^ (-1 / 8 : ℝ) * b ^ (-1 / 4 : ℝ))) := by
          rw [Real.div_rpow ha.le hb.le, Real.div_rpow ha.le hb.le,
            show (-1 / 8 : ℝ) = -(1 / 8 : ℝ) by norm_num, Real.rpow_neg hb.le,
            show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by norm_num, Real.rpow_neg hb.le]
          ring
      _ = 2 * a ^ (-5 / 8 : ℝ) * b ^ (-3 / 8 : ℝ) := by
          have ha1 : a ^ (1 / 8 : ℝ) * a ^ (1 / 4 : ℝ) * a⁻¹ = a ^ (-5 / 8 : ℝ) := by
            rw [← Real.rpow_neg_one a, ← Real.rpow_add ha, ← Real.rpow_add ha]
            congr 1; norm_num
          have hb1 : b ^ (-1 / 8 : ℝ) * b ^ (-1 / 4 : ℝ) = b ^ (-3 / 8 : ℝ) := by
            rw [← Real.rpow_add hb]
            congr 1; norm_num
          rw [ha1, hb1]; ring
  · set a : ℝ := j + 1
    set b : ℝ := k + 1
    have ha : 0 < a := by positivity
    have hb : 0 < b := by positivity
    have hM := M_abs_le hjk
    have hshift := shift_ratio_sub_one_le a b (m : ℝ) ha hb (Nat.cast_nonneg m)
    have hdiff : |(a / b) ^ (1 / 8 : ℝ) - 1| ≤ 1 := by
      have hle : a / b ≤ 1 := (div_le_one hb).mpr (by linarith)
      have hle1 : (a / b) ^ (1 / 8 : ℝ) ≤ 1 := Real.rpow_le_one (div_pos ha hb).le hle (by norm_num)
      rw [abs_of_nonpos (sub_nonpos.mpr hle1)]
      have : 0 ≤ (a / b) ^ (1 / 8 : ℝ) := by positivity
      linarith
    have hmax : max a b = b := max_eq_right (by linarith)
    have hmin : min a b = a := min_eq_left (by linarith)
    have hgap : b / 2 ≤ |(j : ℝ) - k| := by
      have hjk' : (j : ℝ) - k = -(b - a) := by simp [a, b]
      rw [hjk', abs_neg, abs_of_nonneg (by linarith)]
      linarith
    have hM' : |M j k| ≤ (b / a) ^ (1 / 4 : ℝ) * (2 / b) := by
      have h1 : (max a b / min a b) ^ (1 / 4 : ℝ) / |(j : ℝ) - k| ≤ (b / a) ^ (1 / 4 : ℝ) / (b / 2) := by
        rw [hmax, hmin]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hgap
      calc |M j k| ≤ (max a b / min a b) ^ (1 / 4 : ℝ) / |(j : ℝ) - k| := by simpa [a, b] using hM
        _ ≤ (b / a) ^ (1 / 4 : ℝ) / (b / 2) := h1
        _ = (b / a) ^ (1 / 4 : ℝ) * (2 / b) := by ring
    have hshift' : |((j + m + 1 : ℝ) / (k + m + 1 : ℝ)) ^ (1 / 8 : ℝ) - 1| ≤ 1 := by
      calc |((j + m + 1 : ℝ) / (k + m + 1 : ℝ)) ^ (1 / 8 : ℝ) - 1|
          = |((a + m) / (b + m)) ^ (1 / 8 : ℝ) - 1| := by simp [a, b, add_assoc, add_comm]
        _ ≤ |(a / b) ^ (1 / 8 : ℝ) - 1| := hshift
        _ ≤ 1 := hdiff
    rw [Kmat, abs_mul]
    calc |((j + m + 1 : ℝ) / (k + m + 1 : ℝ)) ^ (1 / 8 : ℝ) - 1| * |M j k|
        ≤ 1 * ((b / a) ^ (1 / 4 : ℝ) * (2 / b)) :=
          mul_le_mul hshift' hM' (abs_nonneg _) zero_le_one
      _ = 2 * a ^ (-1 / 4 : ℝ) * (b ^ (1 / 4 : ℝ) * b⁻¹) := by
          rw [one_mul, Real.div_rpow hb.le ha.le,
            show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by norm_num, Real.rpow_neg ha.le]
          ring
      _ = 2 * a ^ (-1 / 4 : ℝ) * b ^ (-3 / 4 : ℝ) := by
          have hb1 : b ^ (1 / 4 : ℝ) * b⁻¹ = b ^ (-3 / 4 : ℝ) := by
            rw [← Real.rpow_neg_one b, ← Real.rpow_add hb]
            congr 1; norm_num
          rw [hb1]
  · set a : ℝ := j + 1
    set b : ℝ := k + 1
    have ha : 0 < a := by positivity
    have hb : 0 < b := by positivity
    have hlt1 : a < 2 * b := lt_of_not_ge h2b
    have hlt2 : b < 2 * a := lt_of_not_ge h2a
    have hM := M_abs_le hjk
    have hshift := shift_ratio_sub_one_le a b (m : ℝ) ha hb (Nat.cast_nonneg m)
    have hdiff : |(a / b) ^ (1 / 8 : ℝ) - 1| ≤ 2 * |a - b| / a := by
      have hr := rpow_eighth_sub_one_le a b ha hb
      calc |(a / b) ^ (1 / 8 : ℝ) - 1| ≤ |a - b| / b := hr
        _ ≤ |a - b| / (a / 2) := by
            gcongr
            linarith
        _ = 2 * |a - b| / a := by ring
    have hmax_le : max a b / min a b ≤ 2 := by
      have hmin_pos : 0 < min a b := lt_min ha hb
      rw [div_le_iff₀ hmin_pos]
      rcases le_total a b with hab | hba
      · rw [max_eq_right hab, min_eq_left hab]; linarith
      · rw [max_eq_left hba, min_eq_right hba]; linarith
    have hM' : |M j k| ≤ 2 / |a - b| := by
      have hrp : (max a b / min a b) ^ (1 / 4 : ℝ) ≤ 2 := by
        have h2 : (max a b / min a b) ^ (1 / 4 : ℝ) ≤ 2 ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hmax_le (by norm_num)
        have h2' : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
          have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 / 4 : ℝ) ≤ 1)
          simpa using this
        exact h2.trans h2'
      have hjk_eq : |(j : ℝ) - k| = |a - b| := by simp [a, b]
      calc |M j k| ≤ (max a b / min a b) ^ (1 / 4 : ℝ) / |(j : ℝ) - k| := by simpa [a, b] using hM
        _ ≤ 2 / |a - b| := by rw [hjk_eq]; exact div_le_div_of_nonneg_right hrp (abs_nonneg _)
    have hshift' : |((j + m + 1 : ℝ) / (k + m + 1 : ℝ)) ^ (1 / 8 : ℝ) - 1| ≤ 2 * |a - b| / a := by
      calc |((j + m + 1 : ℝ) / (k + m + 1 : ℝ)) ^ (1 / 8 : ℝ) - 1|
          = |((a + m) / (b + m)) ^ (1 / 8 : ℝ) - 1| := by simp [a, b, add_assoc, add_comm]
        _ ≤ |(a / b) ^ (1 / 8 : ℝ) - 1| := hshift
        _ ≤ 2 * |a - b| / a := hdiff
    have hab_ne : |a - b| ≠ 0 := abs_ne_zero.mpr (by
      intro heq
      apply hjk
      have : (j : ℝ) = k := by simp [a, b] at heq; linarith
      exact Nat.cast_injective this)
    rw [Kmat, abs_mul]
    calc |((j + m + 1 : ℝ) / (k + m + 1 : ℝ)) ^ (1 / 8 : ℝ) - 1| * |M j k|
        ≤ (2 * |a - b| / a) * (2 / |a - b|) :=
          mul_le_mul hshift' hM' (abs_nonneg _) (by positivity)
      _ = 4 * a⁻¹ := by field_simp; norm_num

lemma sum_Icc_rpow_le {q : ℝ} (hq_lt : q < 1) (hq_ne : q ≠ 0) {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) :
    ∑ k ∈ Finset.Icc A B, (k : ℝ) ^ (q - 1) ≤
      (((B : ℝ) ^ q - ((A - 1 : ℕ) : ℝ) ^ q) / q) := by
  have hstep : ∀ k ∈ Finset.Icc A B,
      (k : ℝ) ^ (q - 1) ≤ ((k : ℝ) ^ q - ((k - 1 : ℕ) : ℝ) ^ q) / q := by
    intro k hk
    have hk2 : 2 ≤ k := hA.trans (Finset.mem_Icc.mp hk).1
    have hk1_pos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
      have : 1 ≤ k - 1 := by omega
      exact_mod_cast this
    have hk_gt : ((k - 1 : ℕ) : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : k - 1 < k)
    let f : ℝ → ℝ := fun x => x ^ q / q
    have hcont : ContinuousOn f (Set.Icc ((k - 1 : ℕ) : ℝ) (k : ℝ)) := by
      refine ContinuousOn.div_const ?_ q
      refine ContinuousOn.rpow_const continuousOn_id fun x hx => ?_
      left; exact (hk1_pos.trans_le hx.1).ne'
    have hderiv : ∀ x ∈ Set.Ioo ((k - 1 : ℕ) : ℝ) (k : ℝ), HasDerivAt f (x ^ (q - 1)) x := by
      intro x hx
      have hxpos : 0 < x := hk1_pos.trans hx.1
      have hd := (Real.hasDerivAt_rpow_const (p := q) (Or.inl hxpos.ne')).div_const q
      refine hd.congr_deriv ?_
      field_simp
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f _ hk_gt hcont hderiv
    have hsub1 : (k : ℝ) - ((k - 1 : ℕ) : ℝ) = 1 := by
      have : k = (k - 1) + 1 := by omega
      conv_lhs => rw [this]
      push_cast; ring
    rw [hsub1, div_one] at hslope
    have hcpos : 0 < c := hk1_pos.trans hc.1
    have hcle : c ≤ k := hc.2.le
    have hrpow_le : (k : ℝ) ^ (q - 1) ≤ c ^ (q - 1) :=
      Real.rpow_le_rpow_of_nonpos hcpos hcle (by linarith)
    rw [hslope] at hrpow_le
    calc (k : ℝ) ^ (q - 1) ≤ f k - f (k - 1 : ℕ) := hrpow_le
      _ = ((k : ℝ) ^ q - ((k - 1 : ℕ) : ℝ) ^ q) / q := by simp [f]; ring
  calc ∑ k ∈ Finset.Icc A B, (k : ℝ) ^ (q - 1)
      ≤ ∑ k ∈ Finset.Icc A B, (((k : ℝ) ^ q - ((k - 1 : ℕ) : ℝ) ^ q) / q) :=
        Finset.sum_le_sum hstep
    _ = (∑ k ∈ Finset.Icc A B, ((k : ℝ) ^ q - ((k - 1 : ℕ) : ℝ) ^ q)) / q := by
        rw [← Finset.sum_div]
    _ = ((B : ℝ) ^ q - ((A - 1 : ℕ) : ℝ) ^ q) / q := by
        congr 1
        clear hstep
        induction B, hAB using Nat.le_induction with
        | base => simp
        | succ m hm ih =>
          rw [Finset.sum_Icc_succ_top (by omega : A ≤ m + 1), ih]
          simp only [Nat.add_sub_cancel]
          ring

lemma sum_Icc_one_rpow_le {q : ℝ} (hq_pos : 0 < q) (hq_lt : q < 1) (B : ℕ) :
    ∑ k ∈ Finset.Icc 1 B, (k : ℝ) ^ (q - 1) ≤ 1 + (B : ℝ) ^ q / q := by
  by_cases hB : B < 1
  · have hB0 : B = 0 := by omega
    subst hB0
    simp [Real.zero_rpow hq_pos.ne']
  · by_cases hB2 : B = 1
    · subst hB2; simp [hq_pos.le]
    · have hB2' : 2 ≤ B := by omega
      have hsplit : Finset.Icc 1 B = insert 1 (Finset.Icc 2 B) := by
        ext k; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
      rw [hsplit, Finset.sum_insert (by simp)]
      have h1 : ((1 : ℕ) : ℝ) ^ (q - 1) = 1 := by simp
      rw [h1]
      have htail := sum_Icc_rpow_le hq_lt hq_pos.ne' (by omega : 2 ≤ 2) hB2'
      have hsub : ((B : ℝ) ^ q - ((2 - 1 : ℕ) : ℝ) ^ q) / q ≤ (B : ℝ) ^ q / q := by
        gcongr
        simp
      linarith

lemma sum_Icc_neg_rpow_le {p : ℝ} (hp : 0 < p) {A B : ℕ} (hA : 2 ≤ A) :
    ∑ k ∈ Finset.Icc A B, (k : ℝ) ^ (-p - 1) ≤ (((A - 1 : ℕ) : ℝ) ^ (-p)) / p := by
  by_cases hAB : B < A
  · rw [Finset.Icc_eq_empty_of_lt hAB, Finset.sum_empty]
    positivity
  · have hAB' : A ≤ B := Nat.le_of_not_lt hAB
    have hq := sum_Icc_rpow_le (q := -p) (by linarith) (by linarith) hA hAB'
    have hB_nonneg : 0 ≤ (B : ℝ) ^ (-p) := by positivity
    have heq : (((B : ℝ) ^ (-p) - ((A - 1 : ℕ) : ℝ) ^ (-p)) / (-p)) =
        (((A - 1 : ℕ) : ℝ) ^ (-p) - (B : ℝ) ^ (-p)) / p := by ring
    rw [heq] at hq
    have hle : (((A - 1 : ℕ) : ℝ) ^ (-p) - (B : ℝ) ^ (-p)) / p ≤ (((A - 1 : ℕ) : ℝ) ^ (-p)) / p := by
      gcongr; linarith
    exact hq.trans hle

noncomputable def uWeight (j : ℕ) : ℝ := (j + 1 : ℝ) ^ (-1 / 2 : ℝ)

lemma uWeight_pos (j : ℕ) : 0 < uWeight j := by unfold uWeight; positivity

lemma schur_row_bound (m j N : ℕ) :
    ∑ k ∈ Finset.range N, |Kmat m j k| * uWeight k ≤ 44 * uWeight j := by
  set a : ℝ := j + 1
  have ha : 0 < a := by positivity
  let S1 := (Finset.range N).filter (fun k => 2 * (k + 1) ≤ j + 1)
  let S2 := (Finset.range N).filter (fun k => ¬ 2 * (k + 1) ≤ j + 1 ∧ ¬ 2 * (j + 1) ≤ k + 1)
  let S3 := (Finset.range N).filter (fun k => 2 * (j + 1) ≤ k + 1)
  have hpart : ∑ k ∈ Finset.range N, |Kmat m j k| * uWeight k =
      (∑ k ∈ S1, |Kmat m j k| * uWeight k) +
      (∑ k ∈ S2, |Kmat m j k| * uWeight k) +
      (∑ k ∈ S3, |Kmat m j k| * uWeight k) := by
    have hsub : Finset.range N = S1 ∪ S2 ∪ S3 := by
      ext k
      simp only [Finset.mem_union, S1, S2, S3, Finset.mem_filter]
      constructor
      · intro hk; refine ?_; tauto
      · rintro ((h | h) | h) <;> exact h.1
    have hd12 : Disjoint S1 S2 := by
      rw [Finset.disjoint_left]; intro k h1 h2
      exact (Finset.mem_filter.mp h2).2.1 (Finset.mem_filter.mp h1).2
    have hd123 : Disjoint (S1 ∪ S2) S3 := by
      rw [Finset.disjoint_left]; intro k h12 h3
      have hk3 := (Finset.mem_filter.mp h3).2
      rcases Finset.mem_union.mp h12 with h1 | h2
      · have hk1 := (Finset.mem_filter.mp h1).2; omega
      · exact (Finset.mem_filter.mp h2).2.2 hk3
    rw [hsub, Finset.sum_union hd123, Finset.sum_union hd12]
  have hS1 : ∑ k ∈ S1, |Kmat m j k| * uWeight k ≤ 18 * uWeight j := by
    have hterm : ∀ k ∈ S1, |Kmat m j k| * uWeight k ≤
        2 * a ^ (-5 / 8 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-7 / 8 : ℝ) := by
      intro k hk
      have hk_cond : 2 * (k + 1) ≤ j + 1 := (Finset.mem_filter.mp hk).2
      have hne : j ≠ k := by omega
      have hk2 : 2 * ((k : ℝ) + 1) ≤ a := by
        change 2 * ((k : ℝ) + 1) ≤ (j : ℝ) + 1
        exact_mod_cast hk_cond
      have hK := Kmat_abs_le m j k
      dsimp only at hK
      rw [if_neg hne, if_pos hk2] at hK
      have hb : (0 : ℝ) < (k + 1 : ℕ) := by positivity
      calc |Kmat m j k| * uWeight k
          ≤ (2 * a ^ (-5 / 8 : ℝ) * ((k : ℝ) + 1) ^ (-3 / 8 : ℝ)) * ((k : ℝ) + 1) ^ (-1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right hK (uWeight_pos k).le
        _ = 2 * a ^ (-5 / 8 : ℝ) * (((k + 1 : ℕ) : ℝ) ^ (-3 / 8 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) := by
            push_cast; ring
        _ = 2 * a ^ (-5 / 8 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-7 / 8 : ℝ) := by
            rw [← Real.rpow_add hb]; congr 2; norm_num
    have hmap : ∑ k ∈ S1, ((k + 1 : ℕ) : ℝ) ^ (-7 / 8 : ℝ) ≤
        ∑ b ∈ Finset.Icc 1 (j + 1), (b : ℝ) ^ (-7 / 8 : ℝ) := by
      have himg : ∑ k ∈ S1, ((k + 1 : ℕ) : ℝ) ^ (-7 / 8 : ℝ) =
          ∑ b ∈ S1.image (fun k : ℕ => k + 1), (b : ℝ) ^ (-7 / 8 : ℝ) :=
        (Finset.sum_image (f := fun b : ℕ => (b : ℝ) ^ (-7 / 8 : ℝ))
          (g := fun k : ℕ => k + 1) (fun _ _ _ _ h => Nat.succ_injective h)).symm
      rw [himg]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
      intro b hb
      rcases Finset.mem_image.mp hb with ⟨k, hk, rfl⟩
      have := (Finset.mem_filter.mp hk).2
      simp only [Finset.mem_Icc]; omega
    have hIcc : ∑ b ∈ Finset.Icc 1 (j + 1), (b : ℝ) ^ (-7 / 8 : ℝ) ≤ 9 * a ^ (1 / 8 : ℝ) := by
      have hq := sum_Icc_one_rpow_le (q := (1 / 8 : ℝ)) (by norm_num) (by norm_num) (j + 1)
      have hpow : (1 / 8 : ℝ) - 1 = -7 / 8 := by norm_num
      rw [hpow] at hq
      have h1 : (1 : ℝ) ≤ a ^ (1 / 8 : ℝ) :=
        Real.one_le_rpow (by dsimp [a]; linarith [show (0 : ℝ) ≤ j by positivity]) (by norm_num)
      have hcast : ((j + 1 : ℕ) : ℝ) = a := by push_cast; rfl
      rw [hcast] at hq
      linarith
    calc ∑ k ∈ S1, |Kmat m j k| * uWeight k
        ≤ ∑ k ∈ S1, (2 * a ^ (-5 / 8 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-7 / 8 : ℝ)) := Finset.sum_le_sum hterm
      _ = 2 * a ^ (-5 / 8 : ℝ) * ∑ k ∈ S1, ((k + 1 : ℕ) : ℝ) ^ (-7 / 8 : ℝ) := by rw [← Finset.mul_sum]
      _ ≤ 2 * a ^ (-5 / 8 : ℝ) * (9 * a ^ (1 / 8 : ℝ)) := by gcongr; exact hmap.trans hIcc
      _ = 18 * (a ^ (-5 / 8 : ℝ) * a ^ (1 / 8 : ℝ)) := by ring
      _ = 18 * uWeight j := by
          rw [← Real.rpow_add ha]; unfold uWeight
          congr 1; norm_num; rfl
  have hS2 : ∑ k ∈ S2, |Kmat m j k| * uWeight k ≤ 16 * uWeight j := by
    have hterm : ∀ k ∈ S2, |Kmat m j k| * uWeight k ≤ 8 * a ^ (-3 / 2 : ℝ) := by
      intro k hk
      have hcond := (Finset.mem_filter.mp hk).2
      have hk_gt : j + 1 < 2 * (k + 1) := Nat.lt_of_not_ge hcond.1
      have hj_gt : k + 1 < 2 * (j + 1) := Nat.lt_of_not_ge hcond.2
      by_cases hjk : j = k
      · subst hjk
        have hev : Even (j + j) := ⟨j, by ring⟩
        simp only [Kmat, M_eq_zero_of_even_add hev, mul_zero, abs_zero, zero_mul]
        positivity
      · have hK := Kmat_abs_le m j k
        dsimp only at hK
        have hn1 : ¬ 2 * ((k : ℝ) + 1) ≤ a := by
          change ¬ 2 * ((k : ℝ) + 1) ≤ (j : ℝ) + 1; exact_mod_cast hcond.1
        have hn2 : ¬ 2 * a ≤ (k : ℝ) + 1 := by
          change ¬ 2 * ((j : ℝ) + 1) ≤ (k : ℝ) + 1; exact_mod_cast hcond.2
        rw [if_neg hjk, if_neg hn1, if_neg hn2] at hK
        have hb_ge : a / 2 ≤ (k : ℝ) + 1 := by
          have : (j + 1 : ℝ) ≤ 2 * ((k : ℝ) + 1) := by exact_mod_cast hk_gt.le
          linarith
        have hu : uWeight k ≤ 2 * a ^ (-1 / 2 : ℝ) := by
          unfold uWeight
          have h1 : ((k : ℝ) + 1) ^ (-1 / 2 : ℝ) ≤ (a / 2) ^ (-1 / 2 : ℝ) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hb_ge (by norm_num)
          have h2 : (a / 2) ^ (-1 / 2 : ℝ) = (2 : ℝ) ^ (1 / 2 : ℝ) * a ^ (-1 / 2 : ℝ) := by
            rw [Real.div_rpow ha.le (by norm_num), div_eq_mul_inv,
              ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
              show -(-1 / 2 : ℝ) = 1 / 2 by norm_num, mul_comm]
          have h2le : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
            simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
          calc uWeight k ≤ (2 : ℝ) ^ (1 / 2 : ℝ) * a ^ (-1 / 2 : ℝ) := h1.trans_eq h2
            _ ≤ 2 * a ^ (-1 / 2 : ℝ) := by gcongr
        calc |Kmat m j k| * uWeight k ≤ (4 * a⁻¹) * (2 * a ^ (-1 / 2 : ℝ)) :=
              mul_le_mul hK hu (uWeight_pos k).le (by positivity)
          _ = 8 * (a⁻¹ * a ^ (-1 / 2 : ℝ)) := by ring
          _ = 8 * a ^ (-3 / 2 : ℝ) := by
              rw [← Real.rpow_neg_one a, ← Real.rpow_add ha]; congr 1; norm_num
    have hcard : (S2.card : ℝ) ≤ 2 * a := by
      have hsub : S2 ⊆ Finset.range (2 * (j + 1)) := by
        intro k hk
        have hcond := (Finset.mem_filter.mp hk).2
        have : k + 1 < 2 * (j + 1) := Nat.lt_of_not_ge hcond.2
        rw [Finset.mem_range]; omega
      have hc : S2.card ≤ 2 * (j + 1) := (Finset.card_le_card hsub).trans (by simp)
      change (S2.card : ℝ) ≤ 2 * ((j : ℝ) + 1)
      exact_mod_cast hc
    calc ∑ k ∈ S2, |Kmat m j k| * uWeight k
        ≤ ∑ _ ∈ S2, (8 * a ^ (-3 / 2 : ℝ)) := Finset.sum_le_sum hterm
      _ = (S2.card : ℝ) * (8 * a ^ (-3 / 2 : ℝ)) := by simp
      _ ≤ (2 * a) * (8 * a ^ (-3 / 2 : ℝ)) := by gcongr
      _ = 16 * (a ^ (1 : ℝ) * a ^ (-3 / 2 : ℝ)) := by simp [Real.rpow_one]; ring
      _ = 16 * uWeight j := by
          rw [← Real.rpow_add ha]; unfold uWeight
          congr 1; norm_num; rfl
  have hS3 : ∑ k ∈ S3, |Kmat m j k| * uWeight k ≤ 10 * uWeight j := by
    have hterm : ∀ k ∈ S3, |Kmat m j k| * uWeight k ≤
        2 * a ^ (-1 / 4 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
      intro k hk
      have hk_cond : 2 * (j + 1) ≤ k + 1 := (Finset.mem_filter.mp hk).2
      have hne : j ≠ k := by omega
      have hk2 : 2 * a ≤ (k : ℝ) + 1 := by
        change 2 * ((j : ℝ) + 1) ≤ (k : ℝ) + 1; exact_mod_cast hk_cond
      have hn1 : ¬ 2 * ((k : ℝ) + 1) ≤ a := by linarith
      have hK := Kmat_abs_le m j k
      dsimp only at hK
      rw [if_neg hne, if_neg hn1, if_pos hk2] at hK
      have hb : (0 : ℝ) < (k + 1 : ℕ) := by positivity
      calc |Kmat m j k| * uWeight k
          ≤ (2 * a ^ (-1 / 4 : ℝ) * ((k : ℝ) + 1) ^ (-3 / 4 : ℝ)) * ((k : ℝ) + 1) ^ (-1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right hK (uWeight_pos k).le
        _ = 2 * a ^ (-1 / 4 : ℝ) * (((k + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) := by
            push_cast; ring
        _ = 2 * a ^ (-1 / 4 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
            rw [← Real.rpow_add hb]; congr 2; norm_num
    have hmap : ∑ k ∈ S3, ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) ≤
        ∑ b ∈ Finset.Icc (2 * (j + 1)) N, (b : ℝ) ^ (-5 / 4 : ℝ) := by
      have himg : ∑ k ∈ S3, ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) =
          ∑ b ∈ S3.image (fun k : ℕ => k + 1), (b : ℝ) ^ (-5 / 4 : ℝ) :=
        (Finset.sum_image (f := fun b : ℕ => (b : ℝ) ^ (-5 / 4 : ℝ))
          (g := fun k : ℕ => k + 1) (fun _ _ _ _ h => Nat.succ_injective h)).symm
      rw [himg]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
      intro b hb
      rcases Finset.mem_image.mp hb with ⟨k, hk, rfl⟩
      have hf := Finset.mem_filter.mp hk
      have hkr := Finset.mem_range.mp hf.1
      simp only [Finset.mem_Icc]; omega
    have hIcc : ∑ b ∈ Finset.Icc (2 * (j + 1)) N, (b : ℝ) ^ (-5 / 4 : ℝ) ≤ 4 * a ^ (-1 / 4 : ℝ) := by
      have hq := sum_Icc_neg_rpow_le (p := (1 / 4 : ℝ)) (by norm_num) (A := 2 * (j + 1)) (B := N) (by omega)
      have hpow : (-1 / 4 : ℝ) - 1 = -5 / 4 := by norm_num
      rw [show -(1 / 4 : ℝ) - 1 = -5 / 4 by norm_num] at hq
      have hA1 : a ≤ ((2 * (j + 1) - 1 : ℕ) : ℝ) := by
        change (j : ℝ) + 1 ≤ ((2 * (j + 1) - 1 : ℕ) : ℝ)
        exact_mod_cast (by omega : j + 1 ≤ 2 * (j + 1) - 1)
      have hr : ((2 * (j + 1) - 1 : ℕ) : ℝ) ^ (-1 / 4 : ℝ) ≤ a ^ (-1 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos ha hA1 (by norm_num)
      linarith
    calc ∑ k ∈ S3, |Kmat m j k| * uWeight k
        ≤ ∑ k ∈ S3, (2 * a ^ (-1 / 4 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ)) := Finset.sum_le_sum hterm
      _ = 2 * a ^ (-1 / 4 : ℝ) * ∑ k ∈ S3, ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by rw [← Finset.mul_sum]
      _ ≤ 2 * a ^ (-1 / 4 : ℝ) * (4 * a ^ (-1 / 4 : ℝ)) := by gcongr; exact hmap.trans hIcc
      _ = 8 * (a ^ (-1 / 4 : ℝ) * a ^ (-1 / 4 : ℝ)) := by ring
      _ ≤ 10 * uWeight j := by
          rw [← Real.rpow_add ha]; unfold uWeight
          have heq : (-1 / 4 : ℝ) + (-1 / 4 : ℝ) = -1 / 2 := by norm_num
          rw [heq]
          linarith [show 0 ≤ a ^ (-1 / 2 : ℝ) by positivity]
  linarith

lemma schur_col_bound (m k N : ℕ) :
    ∑ j ∈ Finset.range N, |Kmat m j k| * uWeight j ≤ 50 * uWeight k := by
  set b : ℝ := k + 1
  have hb : 0 < b := by positivity
  let T1 := (Finset.range N).filter (fun j => 2 * (k + 1) ≤ j + 1)
  let T2 := (Finset.range N).filter (fun j => ¬ 2 * (k + 1) ≤ j + 1 ∧ ¬ 2 * (j + 1) ≤ k + 1)
  let T3 := (Finset.range N).filter (fun j => 2 * (j + 1) ≤ k + 1)
  have hpart : ∑ j ∈ Finset.range N, |Kmat m j k| * uWeight j =
      (∑ j ∈ T1, |Kmat m j k| * uWeight j) +
      (∑ j ∈ T2, |Kmat m j k| * uWeight j) +
      (∑ j ∈ T3, |Kmat m j k| * uWeight j) := by
    have hsub : Finset.range N = T1 ∪ T2 ∪ T3 := by
      ext j
      simp only [Finset.mem_union, T1, T2, T3, Finset.mem_filter]
      constructor
      · intro hj; refine ?_; tauto
      · rintro ((h | h) | h) <;> exact h.1
    have hd12 : Disjoint T1 T2 := by
      rw [Finset.disjoint_left]; intro j h1 h2
      exact (Finset.mem_filter.mp h2).2.1 (Finset.mem_filter.mp h1).2
    have hd123 : Disjoint (T1 ∪ T2) T3 := by
      rw [Finset.disjoint_left]; intro j h12 h3
      have hj3 := (Finset.mem_filter.mp h3).2
      rcases Finset.mem_union.mp h12 with h1 | h2
      · have hj1 := (Finset.mem_filter.mp h1).2; omega
      · exact (Finset.mem_filter.mp h2).2.2 hj3
    rw [hsub, Finset.sum_union hd123, Finset.sum_union hd12]
  have hT1 : ∑ j ∈ T1, |Kmat m j k| * uWeight j ≤ 16 * uWeight k := by
    have hterm : ∀ j ∈ T1, |Kmat m j k| * uWeight j ≤
        2 * b ^ (-3 / 8 : ℝ) * ((j + 1 : ℕ) : ℝ) ^ (-9 / 8 : ℝ) := by
      intro j hj
      have hj_cond : 2 * (k + 1) ≤ j + 1 := (Finset.mem_filter.mp hj).2
      have hne : j ≠ k := by omega
      have hj2 : 2 * b ≤ (j : ℝ) + 1 := by
        change 2 * ((k : ℝ) + 1) ≤ (j : ℝ) + 1; exact_mod_cast hj_cond
      have hK := Kmat_abs_le m j k
      dsimp only at hK
      rw [if_neg hne, if_pos hj2] at hK
      have ha : (0 : ℝ) < (j + 1 : ℕ) := by positivity
      calc |Kmat m j k| * uWeight j
          ≤ (2 * ((j : ℝ) + 1) ^ (-5 / 8 : ℝ) * b ^ (-3 / 8 : ℝ)) * ((j : ℝ) + 1) ^ (-1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right hK (uWeight_pos j).le
        _ = 2 * b ^ (-3 / 8 : ℝ) * (((j + 1 : ℕ) : ℝ) ^ (-5 / 8 : ℝ) * ((j + 1 : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) := by
            push_cast; ring
        _ = 2 * b ^ (-3 / 8 : ℝ) * ((j + 1 : ℕ) : ℝ) ^ (-9 / 8 : ℝ) := by
            rw [← Real.rpow_add ha]; congr 2; norm_num
    have hmap : ∑ j ∈ T1, ((j + 1 : ℕ) : ℝ) ^ (-9 / 8 : ℝ) ≤
        ∑ a ∈ Finset.Icc (2 * (k + 1)) N, (a : ℝ) ^ (-9 / 8 : ℝ) := by
      have himg : ∑ j ∈ T1, ((j + 1 : ℕ) : ℝ) ^ (-9 / 8 : ℝ) =
          ∑ a ∈ T1.image (fun j : ℕ => j + 1), (a : ℝ) ^ (-9 / 8 : ℝ) :=
        (Finset.sum_image (f := fun a : ℕ => (a : ℝ) ^ (-9 / 8 : ℝ))
          (g := fun j : ℕ => j + 1) (fun _ _ _ _ h => Nat.succ_injective h)).symm
      rw [himg]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
      intro a ha
      rcases Finset.mem_image.mp ha with ⟨j, hj, rfl⟩
      have hf := Finset.mem_filter.mp hj
      have hjr := Finset.mem_range.mp hf.1
      simp only [Finset.mem_Icc]; omega
    have hIcc : ∑ a ∈ Finset.Icc (2 * (k + 1)) N, (a : ℝ) ^ (-9 / 8 : ℝ) ≤ 8 * b ^ (-1 / 8 : ℝ) := by
      have hq := sum_Icc_neg_rpow_le (p := (1 / 8 : ℝ)) (by norm_num) (A := 2 * (k + 1)) (B := N) (by omega)
      rw [show -(1 / 8 : ℝ) - 1 = -9 / 8 by norm_num] at hq
      have hA1 : b ≤ ((2 * (k + 1) - 1 : ℕ) : ℝ) := by
        change (k : ℝ) + 1 ≤ ((2 * (k + 1) - 1 : ℕ) : ℝ)
        exact_mod_cast (by omega : k + 1 ≤ 2 * (k + 1) - 1)
      have hr : ((2 * (k + 1) - 1 : ℕ) : ℝ) ^ (-1 / 8 : ℝ) ≤ b ^ (-1 / 8 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hb hA1 (by norm_num)
      linarith
    calc ∑ j ∈ T1, |Kmat m j k| * uWeight j
        ≤ ∑ j ∈ T1, (2 * b ^ (-3 / 8 : ℝ) * ((j + 1 : ℕ) : ℝ) ^ (-9 / 8 : ℝ)) := Finset.sum_le_sum hterm
      _ = 2 * b ^ (-3 / 8 : ℝ) * ∑ j ∈ T1, ((j + 1 : ℕ) : ℝ) ^ (-9 / 8 : ℝ) := by rw [← Finset.mul_sum]
      _ ≤ 2 * b ^ (-3 / 8 : ℝ) * (8 * b ^ (-1 / 8 : ℝ)) := by gcongr; exact hmap.trans hIcc
      _ = 16 * (b ^ (-3 / 8 : ℝ) * b ^ (-1 / 8 : ℝ)) := by ring
      _ = 16 * uWeight k := by
          rw [← Real.rpow_add hb]; unfold uWeight
          congr 1; norm_num; rfl
  have hT2 : ∑ j ∈ T2, |Kmat m j k| * uWeight j ≤ 24 * uWeight k := by
    have hterm : ∀ j ∈ T2, |Kmat m j k| * uWeight j ≤ 12 * b ^ (-3 / 2 : ℝ) := by
      intro j hj
      have hcond := (Finset.mem_filter.mp hj).2
      have hk_gt : j + 1 < 2 * (k + 1) := Nat.lt_of_not_ge hcond.1
      have hj_gt : k + 1 < 2 * (j + 1) := Nat.lt_of_not_ge hcond.2
      by_cases hjk : j = k
      · subst hjk
        have hev : Even (j + j) := ⟨j, by ring⟩
        simp only [Kmat, M_eq_zero_of_even_add hev, mul_zero, abs_zero, zero_mul]
        positivity
      · have hK := Kmat_abs_le m j k
        dsimp only at hK
        have hn1 : ¬ 2 * b ≤ (j : ℝ) + 1 := by
          change ¬ 2 * ((k : ℝ) + 1) ≤ (j : ℝ) + 1; exact_mod_cast hcond.1
        have hn2 : ¬ 2 * ((j : ℝ) + 1) ≤ b := by
          change ¬ 2 * ((j : ℝ) + 1) ≤ (k : ℝ) + 1; exact_mod_cast hcond.2
        rw [if_neg hjk, if_neg hn1, if_neg hn2] at hK
        have ha_ge : b / 2 ≤ (j : ℝ) + 1 := by
          have : (k + 1 : ℝ) ≤ 2 * ((j : ℝ) + 1) := by exact_mod_cast hj_gt.le
          linarith
        have ha_pos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
        have hu : ((j : ℝ) + 1)⁻¹ * uWeight j ≤ 3 * b ^ (-3 / 2 : ℝ) := by
          have hpow_eq : ((j : ℝ) + 1)⁻¹ * uWeight j = ((j : ℝ) + 1) ^ (-3 / 2 : ℝ) := by
            unfold uWeight
            rw [← Real.rpow_neg_one, ← Real.rpow_add ha_pos]
            congr 1; norm_num
          rw [hpow_eq]
          have h1 : ((j : ℝ) + 1) ^ (-3 / 2 : ℝ) ≤ (b / 2) ^ (-3 / 2 : ℝ) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) ha_ge (by norm_num)
          have h2 : (b / 2) ^ (-3 / 2 : ℝ) = (2 : ℝ) ^ (3 / 2 : ℝ) * b ^ (-3 / 2 : ℝ) := by
            rw [Real.div_rpow hb.le (by norm_num), div_eq_mul_inv,
              ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
              show -(-3 / 2 : ℝ) = 3 / 2 by norm_num, mul_comm]
          have h2le : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 3 := by
            have hpow3 : ((2 : ℝ) ^ (3 / 2 : ℝ)) ^ (2 : ℝ) ≤ (3 : ℝ) ^ (2 : ℝ) := by
              rw [← Real.rpow_mul (by norm_num)]
              norm_num
            rw [← Real.rpow_le_rpow_iff (by positivity) (by positivity) (by norm_num : (0 : ℝ) < 2)]
            simpa [Real.rpow_natCast] using hpow3
          calc ((j : ℝ) + 1) ^ (-3 / 2 : ℝ) ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * b ^ (-3 / 2 : ℝ) := h1.trans_eq h2
            _ ≤ 3 * b ^ (-3 / 2 : ℝ) := by gcongr
        calc |Kmat m j k| * uWeight j ≤ (4 * ((j : ℝ) + 1)⁻¹) * uWeight j :=
              mul_le_mul_of_nonneg_right hK (uWeight_pos j).le
          _ = 4 * (((j : ℝ) + 1)⁻¹ * uWeight j) := by ring
          _ ≤ 4 * (3 * b ^ (-3 / 2 : ℝ)) := by gcongr
          _ = 12 * b ^ (-3 / 2 : ℝ) := by ring
    have hcard : (T2.card : ℝ) ≤ 2 * b := by
      have hsub : T2 ⊆ Finset.range (2 * (k + 1)) := by
        intro j hj
        have hcond := (Finset.mem_filter.mp hj).2
        have : j + 1 < 2 * (k + 1) := Nat.lt_of_not_ge hcond.1
        rw [Finset.mem_range]; omega
      have hc : T2.card ≤ 2 * (k + 1) := (Finset.card_le_card hsub).trans (by simp)
      change (T2.card : ℝ) ≤ 2 * ((k : ℝ) + 1)
      exact_mod_cast hc
    calc ∑ j ∈ T2, |Kmat m j k| * uWeight j
        ≤ ∑ _ ∈ T2, (12 * b ^ (-3 / 2 : ℝ)) := Finset.sum_le_sum hterm
      _ = (T2.card : ℝ) * (12 * b ^ (-3 / 2 : ℝ)) := by simp
      _ ≤ (2 * b) * (12 * b ^ (-3 / 2 : ℝ)) := by gcongr
      _ = 24 * (b ^ (1 : ℝ) * b ^ (-3 / 2 : ℝ)) := by simp [Real.rpow_one]; ring
      _ = 24 * uWeight k := by
          rw [← Real.rpow_add hb]; unfold uWeight
          congr 1; norm_num; rfl
  have hT3 : ∑ j ∈ T3, |Kmat m j k| * uWeight j ≤ 10 * uWeight k := by
    have hterm : ∀ j ∈ T3, |Kmat m j k| * uWeight j ≤
        2 * b ^ (-3 / 4 : ℝ) * ((j + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) := by
      intro j hj
      have hj_cond : 2 * (j + 1) ≤ k + 1 := (Finset.mem_filter.mp hj).2
      have hne : j ≠ k := by omega
      have hj2 : 2 * ((j : ℝ) + 1) ≤ b := by
        change 2 * ((j : ℝ) + 1) ≤ (k : ℝ) + 1; exact_mod_cast hj_cond
      have hn1 : ¬ 2 * b ≤ (j : ℝ) + 1 := by linarith
      have hK := Kmat_abs_le m j k
      dsimp only at hK
      rw [if_neg hne, if_neg hn1, if_pos hj2] at hK
      have ha : (0 : ℝ) < (j + 1 : ℕ) := by positivity
      calc |Kmat m j k| * uWeight j
          ≤ (2 * ((j : ℝ) + 1) ^ (-1 / 4 : ℝ) * b ^ (-3 / 4 : ℝ)) * ((j : ℝ) + 1) ^ (-1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right hK (uWeight_pos j).le
        _ = 2 * b ^ (-3 / 4 : ℝ) * (((j + 1 : ℕ) : ℝ) ^ (-1 / 4 : ℝ) * ((j + 1 : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) := by
            push_cast; ring
        _ = 2 * b ^ (-3 / 4 : ℝ) * ((j + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) := by
            rw [← Real.rpow_add ha]; congr 2; norm_num
    have hmap : ∑ j ∈ T3, ((j + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) ≤
        ∑ a ∈ Finset.Icc 1 (k + 1), (a : ℝ) ^ (-3 / 4 : ℝ) := by
      have himg : ∑ j ∈ T3, ((j + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) =
          ∑ a ∈ T3.image (fun j : ℕ => j + 1), (a : ℝ) ^ (-3 / 4 : ℝ) :=
        (Finset.sum_image (f := fun a : ℕ => (a : ℝ) ^ (-3 / 4 : ℝ))
          (g := fun j : ℕ => j + 1) (fun _ _ _ _ h => Nat.succ_injective h)).symm
      rw [himg]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
      intro a ha
      rcases Finset.mem_image.mp ha with ⟨j, hj, rfl⟩
      have := (Finset.mem_filter.mp hj).2
      simp only [Finset.mem_Icc]; omega
    have hIcc : ∑ a ∈ Finset.Icc 1 (k + 1), (a : ℝ) ^ (-3 / 4 : ℝ) ≤ 5 * b ^ (1 / 4 : ℝ) := by
      have hq := sum_Icc_one_rpow_le (q := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (k + 1)
      have hpow : (1 / 4 : ℝ) - 1 = -3 / 4 := by norm_num
      rw [hpow] at hq
      have h1 : (1 : ℝ) ≤ b ^ (1 / 4 : ℝ) :=
        Real.one_le_rpow (by dsimp [b]; linarith [show (0 : ℝ) ≤ k by positivity]) (by norm_num)
      have hcast : ((k + 1 : ℕ) : ℝ) = b := by push_cast; rfl
      rw [hcast] at hq
      linarith
    calc ∑ j ∈ T3, |Kmat m j k| * uWeight j
        ≤ ∑ j ∈ T3, (2 * b ^ (-3 / 4 : ℝ) * ((j + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ)) := Finset.sum_le_sum hterm
      _ = 2 * b ^ (-3 / 4 : ℝ) * ∑ j ∈ T3, ((j + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) := by rw [← Finset.mul_sum]
      _ ≤ 2 * b ^ (-3 / 4 : ℝ) * (5 * b ^ (1 / 4 : ℝ)) := by gcongr; exact hmap.trans hIcc
      _ = 10 * (b ^ (-3 / 4 : ℝ) * b ^ (1 / 4 : ℝ)) := by ring
      _ = 10 * uWeight k := by
          rw [← Real.rpow_add hb]; unfold uWeight
          congr 1; norm_num; rfl
  linarith

lemma schur_test_fin {N : ℕ} (K : ℕ → ℕ → ℝ) (u : ℕ → ℝ) (C₁ C₂ : ℝ)
    (hu : ∀ i, 0 < u i) (hC₁ : 0 ≤ C₁) (_hC₂ : 0 ≤ C₂)
    (hrow : ∀ j < N, ∑ k ∈ Finset.range N, |K j k| * u k ≤ C₁ * u j)
    (hcol : ∀ k < N, ∑ j ∈ Finset.range N, |K j k| * u j ≤ C₂ * u k)
    (a : ℕ → ℝ) :
    ∑ j ∈ Finset.range N, (∑ k ∈ Finset.range N, K j k * a k) ^ 2 ≤
      C₁ * C₂ * ∑ k ∈ Finset.range N, (a k) ^ 2 := by
  have hj_bound : ∀ j ∈ Finset.range N,
      (∑ k ∈ Finset.range N, K j k * a k) ^ 2 ≤
        (C₁ * u j) * ∑ k ∈ Finset.range N, (|K j k| / u k) * (a k) ^ 2 := by
    intro j hj
    have hjN : j < N := Finset.mem_range.mp hj
    have habs : |∑ k ∈ Finset.range N, K j k * a k| ≤
        ∑ k ∈ Finset.range N, Real.sqrt (|K j k| * u k) * (Real.sqrt (|K j k| / u k) * |a k|) := by
      calc |∑ k ∈ Finset.range N, K j k * a k|
          ≤ ∑ k ∈ Finset.range N, |K j k * a k| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k ∈ Finset.range N, Real.sqrt (|K j k| * u k) * (Real.sqrt (|K j k| / u k) * |a k|) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            have huk : 0 < u k := hu k
            rw [abs_mul, ← mul_assoc, ← Real.sqrt_mul (by positivity),
              show (|K j k| * u k) * (|K j k| / u k) = |K j k| ^ 2 by field_simp,
              Real.sqrt_sq (abs_nonneg _)]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N)
      (fun k => Real.sqrt (|K j k| * u k)) (fun k => Real.sqrt (|K j k| / u k) * |a k|)
    have hsq1 : (∑ k ∈ Finset.range N, (Real.sqrt (|K j k| * u k)) ^ 2) =
        ∑ k ∈ Finset.range N, |K j k| * u k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      have huk := (hu k).le
      exact Real.sq_sqrt (mul_nonneg (abs_nonneg _) huk)
    have hsq2 : (∑ k ∈ Finset.range N, (Real.sqrt (|K j k| / u k) * |a k|) ^ 2) =
        ∑ k ∈ Finset.range N, (|K j k| / u k) * (a k) ^ 2 := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_pow, Real.sq_sqrt (div_nonneg (abs_nonneg _) (hu k).le), sq_abs]
    rw [hsq1, hsq2] at hcs
    have hsq_le : (∑ k ∈ Finset.range N, K j k * a k) ^ 2 ≤
        (∑ k ∈ Finset.range N, |K j k| * u k) * ∑ k ∈ Finset.range N, (|K j k| / u k) * (a k) ^ 2 := by
      rw [← sq_abs (∑ k ∈ Finset.range N, K j k * a k)]
      exact (pow_le_pow_left₀ (abs_nonneg _) habs 2).trans hcs
    exact hsq_le.trans (mul_le_mul_of_nonneg_right (hrow j hjN)
      (Finset.sum_nonneg fun k _ => mul_nonneg (div_nonneg (abs_nonneg _) (hu k).le) (sq_nonneg _)))
  calc ∑ j ∈ Finset.range N, (∑ k ∈ Finset.range N, K j k * a k) ^ 2
      ≤ ∑ j ∈ Finset.range N, (C₁ * u j) * ∑ k ∈ Finset.range N, (|K j k| / u k) * (a k) ^ 2 :=
        Finset.sum_le_sum hj_bound
    _ = C₁ * ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, u j * ((|K j k| / u k) * (a k) ^ 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_assoc, Finset.mul_sum]
    _ = C₁ * ∑ k ∈ Finset.range N, ((a k) ^ 2 / u k) * ∑ j ∈ Finset.range N, |K j k| * u j := by
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ ≤ C₁ * ∑ k ∈ Finset.range N, ((a k) ^ 2 / u k) * (C₂ * u k) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk => ?_) hC₁
        exact mul_le_mul_of_nonneg_left (hcol k (Finset.mem_range.mp hk))
          (div_nonneg (sq_nonneg _) (hu k).le)
    _ = C₁ * C₂ * ∑ k ∈ Finset.range N, (a k) ^ 2 := by
        have hfin : ∑ k ∈ Finset.range N, ((a k) ^ 2 / u k) * (C₂ * u k) =
            C₂ * ∑ k ∈ Finset.range N, (a k) ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          have huk : u k ≠ 0 := (hu k).ne'
          field_simp
        rw [hfin, mul_assoc]

lemma integrable_gaussianReal_of_mul_phi {f : ℝ → ℝ} (hmeas : AEStronglyMeasurable f volume)
    (hint : Integrable (fun x => f x * phi x) volume) :
    Integrable f (ProbabilityTheory.gaussianReal 0 1) := by
  have hm : AEStronglyMeasurable f (ProbabilityTheory.gaussianReal 0 1) :=
    hmeas.mono_ac (ProbabilityTheory.gaussianReal_absolutelyContinuous 0 one_ne_zero)
  refine ⟨hm, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, ProbabilityTheory.gaussianReal_of_var_ne_zero 0 one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul₀
      (ProbabilityTheory.measurable_gaussianPDF 0 1).aemeasurable hmeas.aemeasurable.enorm]
  have heq : (fun x : ℝ => (ProbabilityTheory.gaussianPDF 0 1 * fun y => ‖f y‖ₑ) x) =
      fun x => ‖f x * phi x‖ₑ := by
    ext x
    simp only [Pi.mul_apply, ProbabilityTheory.gaussianPDF, phi]
    rw [enorm_mul, Real.enorm_eq_ofReal_abs (ProbabilityTheory.gaussianPDFReal 0 1 x),
      abs_of_pos (ProbabilityTheory.gaussianPDFReal_pos 0 1 x one_ne_zero), mul_comm]
  rw [heq, ← hasFiniteIntegral_iff_enorm]
  exact hint.hasFiniteIntegral

lemma integrable_h1D_mul_h1D (j k : ℕ) :
    Integrable (fun x : ℝ => h1D j x * h1D k x) (ProbabilityTheory.gaussianReal 0 1) := by
  have hmeas : Measurable (fun x : ℝ => h1D j x * h1D k x) :=
    (continuous_h1D j).measurable.mul (continuous_h1D k).measurable
  exact integrable_gaussianReal_of_mul_phi hmeas.aestronglyMeasurable
    (integrable_h1D_mul_h1D_mul_phi j k)

lemma integrable_sgn_mul_h1D_mul_h1D (j k : ℕ) :
    Integrable (fun x : ℝ => (sgn x : ℝ) * h1D j x * h1D k x)
      (ProbabilityTheory.gaussianReal 0 1) := by
  have hsgn_meas : Measurable (fun x : ℝ => (sgn x : ℝ)) :=
    measurable_from_top.comp (Measurable.ite measurableSet_Ici measurable_const measurable_const)
  have hmeas : Measurable (fun x : ℝ => (sgn x : ℝ) * h1D j x * h1D k x) :=
    (hsgn_meas.mul (continuous_h1D j).measurable).mul (continuous_h1D k).measurable
  refine integrable_gaussianReal_of_mul_phi hmeas.aestronglyMeasurable ?_
  refine (integrable_h1D_mul_h1D_mul_phi j k).norm.mono'
    (hmeas.mul measurable_phi).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  have habs_sgn : |(sgn x : ℝ)| = 1 := by simp only [sgn]; split_ifs <;> norm_num
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, habs_sgn, one_mul,
    ← abs_mul, ← abs_mul]

lemma bessel_M_fin (N : ℕ) (b : ℕ → ℝ) :
    ∑ j ∈ Finset.range N, (∑ k ∈ Finset.range N, M j k * b k) ^ 2 ≤
      ∑ k ∈ Finset.range N, (b k) ^ 2 := by
  let c : ℕ → ℝ := fun j => ∑ k ∈ Finset.range N, M j k * b k
  let f : ℝ → ℝ := fun x => ∑ k ∈ Finset.range N, b k * h1D k x
  let g : ℝ → ℝ := fun x => ∑ j ∈ Finset.range N, c j * h1D j x
  have hsf_int : Integrable (fun x => ((sgn x : ℝ) * f x) ^ 2)
      (ProbabilityTheory.gaussianReal 0 1) := by
    have heq : (fun x => ((sgn x : ℝ) * f x) ^ 2) =
        fun x => ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, (b k * b l) * (h1D k x * h1D l x) := by
      ext x
      have hsgn2 : (sgn x : ℝ) ^ 2 = 1 := by simp only [sgn]; split_ifs <;> norm_num
      dsimp only [f]
      rw [mul_pow, hsgn2, one_mul, sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [heq]
    exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
      (integrable_h1D_mul_h1D k l).const_mul _
  have hfg_eq : (fun x => (sgn x : ℝ) * f x * g x) =
      fun x => ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        (c j * b k) * ((sgn x : ℝ) * h1D j x * h1D k x) := by
    ext x
    dsimp only [f, g]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm _ (c j * h1D j x), ← mul_assoc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hfg_int : Integrable (fun x => (sgn x : ℝ) * f x * g x)
      (ProbabilityTheory.gaussianReal 0 1) := by
    rw [hfg_eq]
    exact integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      (integrable_sgn_mul_h1D_mul_h1D j k).const_mul _
  have hg2_int : Integrable (fun x => (g x) ^ 2) (ProbabilityTheory.gaussianReal 0 1) := by
    have heq : (fun x => (g x) ^ 2) =
        fun x => ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N, (c j * c l) * (h1D j x * h1D l x) := by
      ext x
      dsimp only [g]
      rw [sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [heq]
    exact integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
      (integrable_h1D_mul_h1D j l).const_mul _
  have hnorm_ortho : ∀ a : ℕ → ℝ,
      ∫ x, (∑ k ∈ Finset.range N, a k * h1D k x) ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1) =
        ∑ k ∈ Finset.range N, (a k) ^ 2 := by
    intro a
    have heq : (fun x => (∑ k ∈ Finset.range N, a k * h1D k x) ^ 2) =
        fun x => ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, (a k * a l) * (h1D k x * h1D l x) := by
      ext x
      rw [sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [heq, integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
      (integrable_h1D_mul_h1D k l).const_mul _]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [integral_finsetSum _ fun l _ => (integrable_h1D_mul_h1D k l).const_mul _]
    simp_rw [integral_const_mul, h1D_orthonormal]
    simp [hk, sq]
  have h1 : ∫ x, ((sgn x : ℝ) * f x) ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1) =
      ∑ k ∈ Finset.range N, (b k) ^ 2 := by
    have heq : (fun x => ((sgn x : ℝ) * f x) ^ 2) = fun x => (f x) ^ 2 := by
      ext x
      have hsgn2 : (sgn x : ℝ) ^ 2 = 1 := by simp only [sgn]; split_ifs <;> norm_num
      rw [mul_pow, hsgn2, one_mul]
    rw [heq]
    exact hnorm_ortho b
  have h2 : ∫ x, (sgn x : ℝ) * f x * g x ∂(ProbabilityTheory.gaussianReal 0 1) =
      ∑ j ∈ Finset.range N, (c j) ^ 2 := by
    rw [hfg_eq, integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      (integrable_sgn_mul_h1D_mul_h1D j k).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun k _ => (integrable_sgn_mul_h1D_mul_h1D j k).const_mul _]
    simp_rw [integral_const_mul]
    calc ∑ k ∈ Finset.range N, (c j * b k) * M j k
        = c j * ∑ k ∈ Finset.range N, M j k * b k := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
      _ = (c j) ^ 2 := by dsimp [c]; rw [sq]
  have h3 : ∫ x, (g x) ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1) =
      ∑ j ∈ Finset.range N, (c j) ^ 2 := hnorm_ortho c
  have hsq_nonneg : 0 ≤ ∫ x, ((sgn x : ℝ) * f x - g x) ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1) :=
    integral_nonneg fun x => sq_nonneg _
  have hexp : (fun x => ((sgn x : ℝ) * f x - g x) ^ 2) =
      fun x => (((sgn x : ℝ) * f x) ^ 2 - 2 * ((sgn x : ℝ) * f x * g x)) + (g x) ^ 2 := by
    ext x; ring
  have hsub_int : Integrable (fun x => ((sgn x : ℝ) * f x) ^ 2 - 2 * ((sgn x : ℝ) * f x * g x))
      (ProbabilityTheory.gaussianReal 0 1) := hsf_int.sub (hfg_int.const_mul 2)
  rw [hexp, integral_add hsub_int hg2_int,
    integral_sub hsf_int (hfg_int.const_mul 2), integral_const_mul, h1, h2, h3] at hsq_nonneg
  linarith

lemma W1D_sgn_mul_fin (m N : ℕ) (b : ℕ → ℝ) :
    ∑ j ∈ Finset.range N, ((j + m + 1 : ℝ) ^ (1 / 4 : ℝ)) *
        (∑ k ∈ Finset.range N, M j k * b k) ^ 2 ≤
      4402 * ∑ k ∈ Finset.range N, ((k + m + 1 : ℝ) ^ (1 / 4 : ℝ)) * (b k) ^ 2 := by
  let a : ℕ → ℝ := fun k => (k + m + 1 : ℝ) ^ (1 / 8 : ℝ) * b k
  have ha_sq : ∀ k, (a k) ^ 2 = (k + m + 1 : ℝ) ^ (1 / 4 : ℝ) * (b k) ^ 2 := by
    intro k
    have hk : (0 : ℝ) ≤ (k + m + 1 : ℝ) := by positivity
    dsimp [a]
    rw [mul_pow, ← Real.rpow_natCast ((k + m + 1 : ℝ) ^ (1 / 8 : ℝ)) 2, ← Real.rpow_mul hk]
    norm_num
  have hsplit : ∀ j : ℕ, ((j + m + 1 : ℝ) ^ (1 / 8 : ℝ)) * (∑ k ∈ Finset.range N, M j k * b k) =
      (∑ k ∈ Finset.range N, M j k * a k) + (∑ k ∈ Finset.range N, Kmat m j k * a k) := by
    intro j
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hj : (0 : ℝ) ≤ (j + m + 1 : ℝ) := by positivity
    have hk : (0 : ℝ) < (k + m + 1 : ℝ) := by positivity
    have hpow : ((j + m + 1 : ℝ) / (k + m + 1 : ℝ)) ^ (1 / 8 : ℝ) * (k + m + 1 : ℝ) ^ (1 / 8 : ℝ) =
        (j + m + 1 : ℝ) ^ (1 / 8 : ℝ) := by
      rw [Real.div_rpow hj hk.le, div_mul_cancel₀ _ (Real.rpow_pos_of_pos hk _).ne']
    dsimp [a, Kmat]
    calc (j + m + 1 : ℝ) ^ (1 / 8 : ℝ) * (M j k * b k)
        = (((j + m + 1 : ℝ) / (k + m + 1 : ℝ)) ^ (1 / 8 : ℝ) * (k + m + 1 : ℝ) ^ (1 / 8 : ℝ)) *
            (M j k * b k) := by rw [hpow]
      _ = M j k * ((k + m + 1 : ℝ) ^ (1 / 8 : ℝ) * b k) +
            ((((j + m + 1 : ℝ) / (k + m + 1 : ℝ)) ^ (1 / 8 : ℝ) - 1) * M j k) *
              ((k + m + 1 : ℝ) ^ (1 / 8 : ℝ) * b k) := by ring
  have hterm : ∀ j : ℕ, ((j + m + 1 : ℝ) ^ (1 / 4 : ℝ)) * (∑ k ∈ Finset.range N, M j k * b k) ^ 2 ≤
      2 * (∑ k ∈ Finset.range N, M j k * a k) ^ 2 +
      2 * (∑ k ∈ Finset.range N, Kmat m j k * a k) ^ 2 := by
    intro j
    have hj : (0 : ℝ) ≤ (j + m + 1 : ℝ) := by positivity
    have hj_sq : (j + m + 1 : ℝ) ^ (1 / 4 : ℝ) = ((j + m + 1 : ℝ) ^ (1 / 8 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast ((j + m + 1 : ℝ) ^ (1 / 8 : ℝ)) 2, ← Real.rpow_mul hj]
      norm_num
    rw [hj_sq, ← mul_pow, hsplit j]
    nlinarith [sq_nonneg
      ((∑ k ∈ Finset.range N, M j k * a k) - ∑ k ∈ Finset.range N, Kmat m j k * a k)]
  have hM := bessel_M_fin N a
  have hK := schur_test_fin (Kmat m) uWeight 44 50 uWeight_pos (by norm_num) (by norm_num)
    (fun j _ => schur_row_bound m j N) (fun k _ => schur_col_bound m k N) a
  calc ∑ j ∈ Finset.range N, ((j + m + 1 : ℝ) ^ (1 / 4 : ℝ)) * (∑ k ∈ Finset.range N, M j k * b k) ^ 2
      ≤ ∑ j ∈ Finset.range N, (2 * (∑ k ∈ Finset.range N, M j k * a k) ^ 2 +
          2 * (∑ k ∈ Finset.range N, Kmat m j k * a k) ^ 2) := Finset.sum_le_sum fun j _ => hterm j
    _ = 2 * (∑ j ∈ Finset.range N, (∑ k ∈ Finset.range N, M j k * a k) ^ 2) +
          2 * (∑ j ∈ Finset.range N, (∑ k ∈ Finset.range N, Kmat m j k * a k) ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (∑ k ∈ Finset.range N, (a k) ^ 2) + 2 * (44 * 50 * ∑ k ∈ Finset.range N, (a k) ^ 2) := by
        gcongr
    _ = 4402 * ∑ k ∈ Finset.range N, ((k + m + 1 : ℝ) ^ (1 / 4 : ℝ)) * (b k) ^ 2 := by
        have hsum : ∑ k ∈ Finset.range N, (a k) ^ 2 =
            ∑ k ∈ Finset.range N, ((k + m + 1 : ℝ) ^ (1 / 4 : ℝ)) * (b k) ^ 2 :=
          Finset.sum_congr rfl fun k _ => ha_sq k
        rw [hsum]; ring


-- Module 2: Multivariate Hermite basis, L² completeness/Parseval, rotation invariance, Lemma 3.4
-- Concatenated inside `namespace AuxTest1D` after `mod1_hermite1d.lean`.

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def γ (n : ℕ) : Measure (E n) := ProbabilityTheory.stdGaussian (E n)

instance isProbabilityMeasure_γ (n : ℕ) : IsProbabilityMeasure (γ n) := by
  unfold γ
  infer_instance

/-- Multivariate probabilists' orthonormal Hermite function. -/
noncomputable def Hnd {n : ℕ} (α : Fin n → ℕ) (g : E n) : ℝ :=
  ∏ i : Fin n, h1D (α i) (g i)

@[fun_prop]
lemma continuous_Hnd {n : ℕ} (α : Fin n → ℕ) : Continuous (Hnd α) := by
  unfold Hnd
  refine continuous_finsetProd _ fun i _ => ?_
  exact (continuous_h1D (α i)).comp (PiLp.continuous_apply 2 (fun _ => ℝ) i)

@[fun_prop]
lemma measurable_Hnd {n : ℕ} (α : Fin n → ℕ) : Measurable (Hnd α) :=
  (continuous_Hnd α).measurable

def totalDeg {n : ℕ} (α : Fin n → ℕ) : ℕ := ∑ i : Fin n, α i

def I_deg (n d : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset (fun _ : Fin n => Finset.range (d + 1))).filter (fun α => totalDeg α ≤ d)

lemma mem_I_deg {n d : ℕ} {α : Fin n → ℕ} : α ∈ I_deg n d ↔ totalDeg α ≤ d := by
  rw [I_deg, Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · exact fun h => h.2
  · intro h
    unfold totalDeg at h
    refine ⟨fun i => Finset.mem_range.mpr ?_, h⟩
    have hle : α i ≤ ∑ j : Fin n, α j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (α j)) (Finset.mem_univ i)
    omega

def I_deg_eq (n d : ℕ) : Finset (Fin n → ℕ) :=
  (I_deg n d).filter (fun α => totalDeg α = d)

lemma mem_I_deg_eq {n d : ℕ} {α : Fin n → ℕ} : α ∈ I_deg_eq n d ↔ totalDeg α = d := by
  simp only [I_deg_eq, Finset.mem_filter, mem_I_deg]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

/-! ### Product Integrability & Orthonormality on `γ n` -/

lemma integrable_pi_fin_prod {n : ℕ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (f : Fin n → ℝ → ℝ) (hf : ∀ i, Integrable (f i) μ) :
    Integrable (fun x : Fin n → ℝ => ∏ i : Fin n, f i (x i)) (Measure.pi fun _ : Fin n => μ) := by
  induction n with
  | zero =>
    simp only [Fin.prod_univ_zero]
    exact integrable_const 1
  | succ m ih =>
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm
    have hmp : MeasurePreserving e
        (μ.prod (Measure.pi fun _ : Fin m => μ)) (Measure.pi fun _ : Fin (m + 1) => μ) :=
      (MeasureTheory.measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0).symm
    rw [← hmp.integrable_comp_emb e.measurableEmbedding]
    have hfun : (fun x : Fin (m + 1) → ℝ => ∏ i : Fin (m + 1), f i (x i)) ∘ ⇑e =
        fun z : ℝ × (Fin m → ℝ) => f 0 z.1 * ∏ j : Fin m, f j.succ (z.2 j) := by
      ext ⟨x0, xtail⟩
      simp only [Function.comp_def, Fin.prod_univ_succ, e, MeasurableEquiv.piFinSuccAbove_symm_apply]
      rfl
    rw [hfun]
    exact (hf 0).smul_prod (ih (fun j => f j.succ) (fun j => hf j.succ))

lemma integrable_Hnd_mul_Hnd {n : ℕ} (α β : Fin n → ℕ) :
    Integrable (fun g : E n => Hnd α g * Hnd β g) (γ n) := by
  rw [γ, ← ProbabilityTheory.map_pi_eq_stdGaussian]
  refine (integrable_map_measure ?_
    (PiLp.lipschitzWith_toLp 2 (fun _ : Fin n => ℝ)).continuous.measurable.aemeasurable).mpr ?_
  · exact ((continuous_Hnd α).fun_mul (continuous_Hnd β)).aestronglyMeasurable
  have heq : (fun x : Fin n → ℝ =>
        Hnd α (WithLp.toLp 2 x) * Hnd β (WithLp.toLp 2 x)) =
      fun x => ∏ i : Fin n, (h1D (α i) (x i) * h1D (β i) (x i)) := by
    ext x
    simp [Hnd, Finset.prod_mul_distrib]
  change Integrable (fun x : Fin n → ℝ => Hnd α (WithLp.toLp 2 x) * Hnd β (WithLp.toLp 2 x)) _
  rw [heq]
  exact integrable_pi_fin_prod _ fun i => integrable_h1D_mul_h1D (α i) (β i)

lemma memLp_Hnd {n : ℕ} (α : Fin n → ℕ) : MemLp (Hnd α) 2 (γ n) := by
  rw [memLp_two_iff_integrable_sq (continuous_Hnd α).aestronglyMeasurable]
  simpa [sq] using integrable_Hnd_mul_Hnd α α

lemma Hnd_orthonormal {n : ℕ} (α β : Fin n → ℕ) :
    ∫ g : E n, Hnd α g * Hnd β g ∂(γ n) = if α = β then 1 else 0 := by
  rw [γ, ← ProbabilityTheory.map_pi_eq_stdGaussian,
    integral_map (PiLp.lipschitzWith_toLp 2 (fun _ : Fin n => ℝ)).continuous.measurable.aemeasurable
      ((continuous_Hnd α).fun_mul (continuous_Hnd β)).aestronglyMeasurable]
  have heq : (fun x : Fin n → ℝ =>
        Hnd α (WithLp.toLp 2 x) * Hnd β (WithLp.toLp 2 x)) =
      fun x => ∏ i : Fin n, (h1D (α i) (x i) * h1D (β i) (x i)) := by
    ext x
    simp [Hnd, Finset.prod_mul_distrib]
  change ∫ x : Fin n → ℝ, Hnd α (WithLp.toLp 2 x) * Hnd β (WithLp.toLp 2 x) ∂_ = _
  rw [heq, integral_fintype_prod_eq_prod (f := fun i x => h1D (α i) x * h1D (β i) x)]
  simp_rw [h1D_orthonormal]
  by_cases h : α = β
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma integrable_exp_mul_inner_γ {n : ℕ} (c : ℝ) (t : E n) :
    Integrable (fun g : E n => Real.exp (c * inner ℝ g t)) (γ n) := by
  rw [γ, ← ProbabilityTheory.map_pi_eq_stdGaussian]
  refine (integrable_map_measure ?_
    (PiLp.lipschitzWith_toLp 2 (fun _ : Fin n => ℝ)).continuous.measurable.aemeasurable).mpr ?_
  · exact (Real.continuous_exp.comp
      (continuous_const.mul (continuous_id.inner continuous_const))).aestronglyMeasurable
  have heq : (fun x : Fin n → ℝ => Real.exp (c * inner ℝ (WithLp.toLp 2 x) t)) =
      fun x => ∏ i : Fin n, Real.exp ((c * t i) * x i) := by
    ext x
    rw [PiLp.inner_apply, Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [RCLike.inner_apply, conj_trivial]
    ring_nf
  change Integrable (fun x : Fin n → ℝ => Real.exp (c * inner ℝ (WithLp.toLp 2 x) t)) _
  rw [heq]
  exact integrable_pi_fin_prod _ fun i => ProbabilityTheory.integrable_exp_mul_gaussianReal _

lemma integrable_mul_of_memLp_two {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {u v : Ω → ℝ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    Integrable (fun x => u x * v x) μ := by
  refine ((hu.integrable_sq.add hv.integrable_sq).div_const 2).mono' (hu.1.mul hv.1)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs]
  dsimp only [Pi.add_apply]
  nlinarith [abs_nonneg (u x), abs_nonneg (v x), abs_mul (u x) (v x),
    sq_abs (u x), sq_abs (v x), sq_nonneg (|u x| - |v x|)]

/-! ### Polynomial Subspaces & Completeness in `L²(γ n; ℝ)` -/

lemma x_mul_h1D_eq (j : ℕ) (x : ℝ) :
    x * h1D j x = Real.sqrt (j + 1 : ℝ) * h1D (j + 1) x +
      (if j = 0 then 0 else Real.sqrt (j : ℝ) * h1D (j - 1) x) := by
  have hsqrt1 : (0 : ℝ) < j + 1 := by positivity
  have hfac1 : Real.sqrt ((j + 1).factorial : ℝ) =
      Real.sqrt (j + 1 : ℝ) * Real.sqrt (j.factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Real.sqrt_mul hsqrt1.le]
  have h1 : Real.sqrt (j + 1 : ℝ) * h1D (j + 1) x =
      (Real.sqrt (j.factorial : ℝ))⁻¹ * Hpoly (j + 1) x := by
    rw [h1D, hfac1, mul_inv]
    have hne : Real.sqrt (j + 1 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hsqrt1
    calc Real.sqrt (j + 1 : ℝ) *
          ((Real.sqrt (j + 1 : ℝ))⁻¹ * (Real.sqrt (j.factorial : ℝ))⁻¹ * Hpoly (j + 1) x)
        = (Real.sqrt (j + 1 : ℝ) * (Real.sqrt (j + 1 : ℝ))⁻¹) *
            ((Real.sqrt (j.factorial : ℝ))⁻¹ * Hpoly (j + 1) x) := by ring
      _ = (Real.sqrt (j.factorial : ℝ))⁻¹ * Hpoly (j + 1) x := by
            rw [mul_inv_cancel₀ hne, one_mul]
  rw [h1, Hpoly_succ j x]
  cases j with
  | zero =>
    simp [h1D]
  | succ k =>
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    have hk : (0 : ℝ) < k + 1 := by positivity
    have hfac2 : Real.sqrt ((k + 1).factorial : ℝ) =
        Real.sqrt (k + 1 : ℝ) * Real.sqrt (k.factorial : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Real.sqrt_mul hk.le]
    have hsq : Real.sqrt (k + 1 : ℝ) * Real.sqrt (k + 1 : ℝ) = (k + 1 : ℝ) :=
      Real.mul_self_sqrt hk.le
    rw [h1D, h1D, hfac2, mul_inv]
    have hne : Real.sqrt (k + 1 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hk
    have hfac_ne : Real.sqrt (k.factorial : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
    field_simp
    push_cast
    rw [mul_right_comm (Real.sqrt ((k : ℝ) + 1)) (Hpoly k x) (Real.sqrt ((k : ℝ) + 1)), hsq]
    ring

noncomputable def P_Hnd (n d : ℕ) : Submodule ℝ (E n → ℝ) :=
  Submodule.span ℝ (Set.image (Hnd : (Fin n → ℕ) → E n → ℝ) (I_deg n d : Set (Fin n → ℕ)))

lemma P_Hnd_mono {n d₁ d₂ : ℕ} (h : d₁ ≤ d₂) : P_Hnd n d₁ ≤ P_Hnd n d₂ := by
  refine Submodule.span_mono (Set.image_mono ?_)
  intro α hα
  exact mem_I_deg.mpr ((mem_I_deg.mp hα).trans h)

lemma mul_coord_mem_P_Hnd {n d : ℕ} {f : E n → ℝ} (hf : f ∈ P_Hnd n d) (i₀ : Fin n) :
    (fun g : E n => g i₀ * f g) ∈ P_Hnd n (d + 1) := by
  induction hf using Submodule.span_induction with
  | mem p hp =>
    rcases hp with ⟨β, hβ, rfl⟩
    have hβ_deg : totalDeg β ≤ d := mem_I_deg.mp hβ
    have hfn : (fun g : E n => g i₀ * Hnd β g) =
        Real.sqrt (β i₀ + 1 : ℝ) • Hnd (Function.update β i₀ (β i₀ + 1)) +
          (if β i₀ = 0 then (0 : E n → ℝ) else
            Real.sqrt (β i₀ : ℝ) • Hnd (Function.update β i₀ (β i₀ - 1))) := by
      ext g
      have hsplit : Hnd β g = h1D (β i₀) (g i₀) *
          ∏ i ∈ Finset.univ.erase i₀, h1D (β i) (g i) := by
        rw [Hnd, ← Finset.mul_prod_erase Finset.univ (fun i => h1D (β i) (g i)) (Finset.mem_univ i₀)]
      have hprod_upd : ∀ k : ℕ, Hnd (Function.update β i₀ k) g =
          h1D k (g i₀) * ∏ i ∈ Finset.univ.erase i₀, h1D (β i) (g i) := by
        intro k
        rw [Hnd, ← Finset.mul_prod_erase Finset.univ
          (fun i => h1D (Function.update β i₀ k i) (g i)) (Finset.mem_univ i₀)]
        simp only [Function.update_self]
        congr 1
        refine Finset.prod_congr rfl fun i hi => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hsplit, ← mul_assoc, x_mul_h1D_eq]
      split_ifs with h0
      · simp only [Pi.zero_apply, add_zero, hprod_upd]; ring
      · simp only [Pi.smul_apply, smul_eq_mul, hprod_upd]; ring
    rw [hfn]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ?_)) ?_
    · refine ⟨Function.update β i₀ (β i₀ + 1), mem_I_deg.mpr ?_, rfl⟩
      have hdeg1 : totalDeg (Function.update β i₀ (β i₀ + 1)) = totalDeg β + 1 := by
        unfold totalDeg
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i₀),
          ← Finset.add_sum_erase Finset.univ β (Finset.mem_univ i₀)]
        simp only [Function.update_self]
        have hs : ∑ i ∈ Finset.univ.erase i₀, Function.update β i₀ (β i₀ + 1) i =
            ∑ i ∈ Finset.univ.erase i₀, β i :=
          Finset.sum_congr rfl fun i hi => Function.update_of_ne (Finset.ne_of_mem_erase hi) _ β
        rw [hs]; omega
      omega
    · split_ifs with h0
      · change (0 : E n → ℝ) ∈ P_Hnd n (d + 1)
        exact (P_Hnd n (d + 1)).zero_mem
      · refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
        refine ⟨Function.update β i₀ (β i₀ - 1), mem_I_deg.mpr ?_, rfl⟩
        have hdeg2 : totalDeg (Function.update β i₀ (β i₀ - 1)) ≤ totalDeg β := by
          unfold totalDeg
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i₀),
            ← Finset.add_sum_erase Finset.univ β (Finset.mem_univ i₀)]
          simp only [Function.update_self]
          have hs : ∑ i ∈ Finset.univ.erase i₀, Function.update β i₀ (β i₀ - 1) i =
              ∑ i ∈ Finset.univ.erase i₀, β i :=
            Finset.sum_congr rfl fun i hi => Function.update_of_ne (Finset.ne_of_mem_erase hi) _ β
          rw [hs]; omega
        omega
  | zero =>
    have h0 : (fun g : E n => g i₀ * (0 : E n → ℝ) g) = 0 := by ext; simp
    rw [h0]
    exact (P_Hnd n (d + 1)).zero_mem
  | add x y _ _ ihx ihy =>
    have hadd : (fun g : E n => g i₀ * (x + y) g) =
        (fun g => g i₀ * x g) + (fun g => g i₀ * y g) := by
      ext g; simp [mul_add]
    rw [hadd]
    exact (P_Hnd n (d + 1)).add_mem ihx ihy
  | smul c x _ ihx =>
    have hsm : (fun g : E n => g i₀ * (c • x) g) = c • (fun g => g i₀ * x g) := by
      ext g; simp [smul_eq_mul]; ring
    rw [hsm]
    exact (P_Hnd n (d + 1)).smul_mem c ihx

lemma mul_inner_mem_P_Hnd {n d : ℕ} {f : E n → ℝ} (hf : f ∈ P_Hnd n d) (u : E n) :
    (fun g : E n => inner ℝ g u * f g) ∈ P_Hnd n (d + 1) := by
  have heq : (fun g : E n => inner ℝ g u * f g) =
      ∑ i : Fin n, u i • (fun g : E n => g i * f g) := by
    ext g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, PiLp.inner_apply, RCLike.inner_apply,
      conj_trivial, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [heq]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (mul_coord_mem_P_Hnd hf i)

lemma one_mem_P_Hnd (n : ℕ) : (fun _ : E n => (1 : ℝ)) ∈ P_Hnd n 0 := by
  have h1 : (fun _ : E n => (1 : ℝ)) = Hnd (0 : Fin n → ℕ) := by
    ext g; simp [Hnd, h1D_zero_fn]
  rw [h1]
  exact Submodule.subset_span ⟨0, mem_I_deg.mpr (by simp [totalDeg]), rfl⟩

lemma mul_pow_inner_mem_P_Hnd {n d k : ℕ} (u : E n) {f : E n → ℝ} (hf : f ∈ P_Hnd n d) :
    (fun g : E n => (inner ℝ g u) ^ k * f g) ∈ P_Hnd n (d + k) := by
  induction k generalizing d f with
  | zero =>
    simpa using hf
  | succ k ih =>
    have heq : (fun g : E n => (inner ℝ g u) ^ (k + 1) * f g) =
        fun g => inner ℝ g u * ((inner ℝ g u) ^ k * f g) := by
      ext g; ring
    rw [heq, ← add_assoc]
    exact mul_inner_mem_P_Hnd (ih hf) u

lemma inner_pow_mem_P_Hnd {n k : ℕ} (u : E n) :
    (fun g : E n => (inner ℝ g u) ^ k) ∈ P_Hnd n k := by
  simpa using mul_pow_inner_mem_P_Hnd u (one_mem_P_Hnd n)

lemma mul_poly_inner_mem_P_Hnd {n d : ℕ} (P : ℝ[X]) (m : ℕ) (hdeg : P.natDegree ≤ m)
    (u : E n) {f : E n → ℝ} (hf : f ∈ P_Hnd n d) :
    (fun g : E n => P.eval (inner ℝ g u) * f g) ∈ P_Hnd n (d + m) := by
  have heq : (fun g : E n => P.eval (inner ℝ g u) * f g) =
      ∑ k ∈ Finset.range (m + 1), P.coeff k • (fun g => (inner ℝ g u) ^ k * f g) := by
    ext g
    rw [Polynomial.eval_eq_sum_range' (lt_of_le_of_lt hdeg (Nat.lt_succ_self m)), Finset.sum_mul]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [heq]
  refine Submodule.sum_mem _ fun k hk => ?_
  have hk_le : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  exact Submodule.smul_mem _ _ (P_Hnd_mono (by omega) (mul_pow_inner_mem_P_Hnd u hf))

lemma exists_poly_h1D (m : ℕ) :
    ∃ P : ℝ[X], P.natDegree ≤ m ∧ ∀ x : ℝ, h1D m x = P.eval x := by
  refine ⟨Polynomial.C (Real.sqrt (m.factorial : ℝ))⁻¹ *
      (Polynomial.hermite m).map (algebraMap ℤ ℝ), ?_, fun x => ?_⟩
  · calc (Polynomial.C (Real.sqrt (m.factorial : ℝ))⁻¹ *
          (Polynomial.hermite m).map (algebraMap ℤ ℝ)).natDegree
        ≤ ((Polynomial.hermite m).map (algebraMap ℤ ℝ)).natDegree :=
          Polynomial.natDegree_C_mul_le _ _
      _ ≤ (Polynomial.hermite m).natDegree := Polynomial.natDegree_map_le
      _ ≤ m := (Polynomial.natDegree_hermite (n := m)).le
  · simp [h1D, Hpoly, Polynomial.aeval_def, Polynomial.eval_map]

lemma Hnd_comp_isom_mem_P_Hnd {n : ℕ} (α : Fin n → ℕ) (R : E n ≃ₗᵢ[ℝ] E n) :
    (Hnd α ∘ R) ∈ P_Hnd n (totalDeg α) := by
  have hu : ∀ i : Fin n, ∃ P : ℝ[X], P.natDegree ≤ α i ∧ ∀ x, h1D (α i) x = P.eval x :=
    fun i => exists_poly_h1D (α i)
  choose P hPdeg hPeq using hu
  let u : Fin n → E n := fun i => R.symm (EuclideanSpace.basisFun (Fin n) ℝ i)
  have hprod : ∀ s : Finset (Fin n),
      (fun g : E n => ∏ i ∈ s, h1D (α i) ((R g) i)) ∈ P_Hnd n (∑ i ∈ s, α i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simpa using one_mem_P_Hnd n
    | @insert i s hi ih =>
      have heq : (fun g : E n => ∏ j ∈ insert i s, h1D (α j) ((R g) j)) =
          fun g => (P i).eval (inner ℝ g (u i)) * (∏ j ∈ s, h1D (α j) ((R g) j)) := by
        ext g
        rw [Finset.prod_insert hi, ← hPeq i]
        congr 2
        dsimp [u]
        rw [← EuclideanSpace.inner_basisFun_real (Fin n) (R g) i, R.inner_map_eq_flip]
      rw [heq, Finset.sum_insert hi, add_comm]
      exact mul_poly_inner_mem_P_Hnd (P i) (α i) (hPdeg i) (u i) ih
  simpa [Function.comp_def, Hnd, totalDeg] using hprod Finset.univ

lemma P_Hnd_memLp {n d : ℕ} {p : E n → ℝ} (hp : p ∈ P_Hnd n d) : MemLp p 2 (γ n) := by
  induction hp using Submodule.span_induction with
  | mem q hq =>
    rcases hq with ⟨α, _, rfl⟩
    exact memLp_Hnd α
  | zero => exact MemLp.zero
  | add x y _ _ ihx ihy => exact ihx.add ihy
  | smul c x _ ihx => exact ihx.const_smul c

lemma integral_P_Hnd_mul_eq_zero {n d : ℕ} {f : E n → ℝ} (hf : MemLp f 2 (γ n))
    (h0 : ∀ α : Fin n → ℕ, ∫ g : E n, Hnd α g * f g ∂(γ n) = 0)
    {p : E n → ℝ} (hp : p ∈ P_Hnd n d) :
    Integrable (fun g : E n => p g * f g) (γ n) ∧ ∫ g : E n, p g * f g ∂(γ n) = 0 := by
  induction hp using Submodule.span_induction with
  | mem q hq =>
    rcases hq with ⟨α, _, rfl⟩
    exact ⟨integrable_mul_of_memLp_two (memLp_Hnd α) hf, h0 α⟩
  | zero =>
    simp
  | add x y _ _ ihx ihy =>
    have hadd : ∀ g : E n, (x + y) g * f g = x g * f g + y g * f g := fun g => add_mul _ _ _
    refine ⟨?_, ?_⟩
    · simp_rw [hadd]; exact ihx.1.add ihy.1
    · simp_rw [hadd]; rw [integral_add ihx.1 ihy.1, ihx.2, ihy.2, add_zero]
  | smul c x _ ihx =>
    have hsm : ∀ g : E n, (c • x) g * f g = c * (x g * f g) := fun g => by
      simp [smul_eq_mul]; ring
    refine ⟨?_, ?_⟩
    · simp_rw [hsm]; exact ihx.1.const_mul c
    · simp_rw [hsm]; rw [integral_const_mul, ihx.2, mul_zero]

lemma tendsto_complex_exp_partial_sums (z : ℂ) :
    Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, z ^ k / (k.factorial : ℂ))
      Filter.atTop (𝓝 (Complex.exp z)) := by
  have hhalf : ∃ N0 : ℕ, ∀ N ≥ N0, ‖z‖ / ((N : ℝ) + 1) ≤ 1 / 2 := by
    refine ⟨Nat.ceil (2 * ‖z‖), fun N hN => ?_⟩
    have hle : 2 * ‖z‖ ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  obtain ⟨N0, hN0⟩ := hhalf
  have hbound : ∀ k : ℕ, ‖z‖ ^ (N0 + k) / ((N0 + k).factorial : ℝ) ≤
      (‖z‖ ^ N0 / (N0.factorial : ℝ)) * (1 / 2 : ℝ) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hratio : ‖z‖ / ((N0 + k : ℕ) + 1 : ℝ) ≤ 1 / 2 := by
        simpa [Nat.cast_add] using hN0 (N0 + k) (by omega)
      calc ‖z‖ ^ (N0 + (k + 1)) / ((N0 + (k + 1)).factorial : ℝ)
          = (‖z‖ ^ (N0 + k) / ((N0 + k).factorial : ℝ)) *
              (‖z‖ / ((N0 + k : ℕ) + 1 : ℝ)) := by
            rw [← Nat.add_assoc, Nat.factorial_succ, pow_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
            have h1 : ((N0 + k : ℕ) + 1 : ℝ) ≠ 0 := by positivity
            have h2 : ((N0 + k).factorial : ℝ) ≠ 0 := by positivity
            field_simp
        _ ≤ ((‖z‖ ^ N0 / (N0.factorial : ℝ)) * (1 / 2 : ℝ) ^ k) * (1 / 2) :=
            mul_le_mul ih hratio (by positivity) (by positivity)
        _ = (‖z‖ ^ N0 / (N0.factorial : ℝ)) * (1 / 2 : ℝ) ^ (k + 1) := by
            rw [pow_succ]; ring
  have hlim_rhs : Filter.Tendsto (fun k : ℕ => (‖z‖ ^ N0 / (N0.factorial : ℝ)) * (1 / 2 : ℝ) ^ k)
      Filter.atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (‖z‖ ^ N0 / (N0.factorial : ℝ))
  have hlim_rhs2 : Filter.Tendsto (fun k : ℕ => 2 * ((‖z‖ ^ N0 / (N0.factorial : ℝ)) * (2 ^ k : ℝ)⁻¹))
      Filter.atTop (𝓝 0) := by
    simpa [one_div, inv_pow] using hlim_rhs.const_mul 2
  have hlim_err : Filter.Tendsto
      (fun N : ℕ => 2 * (‖z‖ ^ N / (N.factorial : ℝ))) Filter.atTop (𝓝 0) := by
    rw [← Filter.tendsto_add_atTop_iff_nat N0]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim_rhs2
      (fun k => by positivity)
      (fun k => mul_le_mul_of_nonneg_left (by simpa [add_comm, one_div, inv_pow] using hbound k) (by norm_num))
  have hlim_diff : Filter.Tendsto
      (fun N : ℕ => Complex.exp z - ∑ k ∈ Finset.range N, z ^ k / (k.factorial : ℂ))
      Filter.atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim_err
      (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_
    filter_upwards [Filter.eventually_ge_atTop N0] with N hN
    have h1 := Complex.exp_bound' (x := z) (n := N) (by simpa [Nat.succ_eq_add_one] using hN0 N hN)
    linarith
  have hsub := tendsto_const_nhds (x := Complex.exp z) |>.sub hlim_diff
  simpa using hsub

lemma integral_Hnd_mul_eq_zero_imp {n : ℕ} {f : E n → ℝ} (hf : MemLp f 2 (γ n))
    (h0 : ∀ α : Fin n → ℕ, ∫ g : E n, Hnd α g * f g ∂(γ n) = 0) :
    f =ᵐ[γ n] 0 := by
  have hchar_int : ∀ t : E n,
      ∫ g : E n, Complex.exp ((inner ℝ g t : ℂ) * Complex.I) * (f g : ℂ) ∂(γ n) = 0 := by
    intro t
    let S : ℕ → E n → ℂ := fun N g =>
      (∑ k ∈ Finset.range N, ((inner ℝ g t : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)) * (f g : ℂ)
    let bound : E n → ℝ := fun g => Real.exp |inner ℝ g t| * |f g|
    have hbound_int : Integrable bound (γ n) := by
      have hdom : Integrable (fun g : E n =>
          (Real.exp (2 * inner ℝ g t) + Real.exp (-2 * inner ℝ g t) + (f g) ^ 2) / 2) (γ n) :=
        (((integrable_exp_mul_inner_γ 2 t).add (integrable_exp_mul_inner_γ (-2) t)).add
          hf.integrable_sq).div_const 2
      refine hdom.mono' ?_ (ae_of_all _ fun g => ?_)
      · exact ((Real.continuous_exp.comp
            (continuous_abs.comp (continuous_id.inner continuous_const))).aestronglyMeasurable.mul
            (continuous_abs.comp_aestronglyMeasurable hf.aestronglyMeasurable))
      · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (abs_nonneg _))]
        have h1 : 2 * (Real.exp |inner ℝ g t| * |f g|) ≤
            (Real.exp |inner ℝ g t|) ^ 2 + |f g| ^ 2 := by
          nlinarith [sq_nonneg (Real.exp |inner ℝ g t| - |f g|)]
        have h2 : (Real.exp |inner ℝ g t|) ^ 2 = Real.exp (2 * |inner ℝ g t|) := by
          rw [sq, ← Real.exp_add, two_mul]
        have h3 : Real.exp (2 * |inner ℝ g t|) ≤
            Real.exp (2 * inner ℝ g t) + Real.exp (-2 * inner ℝ g t) := by
          simpa [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), neg_mul] using
            Real.exp_abs_le (2 * inner ℝ g t)
        rw [sq_abs] at h1
        linarith
    have hS_meas : ∀ N : ℕ, AEStronglyMeasurable (S N) (γ n) := by
      intro N
      have hpoly : Continuous (fun g : E n =>
          ∑ k ∈ Finset.range N, ((inner ℝ g t : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)) := by
        refine continuous_finsetSum _ fun k _ => ?_
        exact (((Complex.continuous_ofReal.comp
          (continuous_id.inner continuous_const)).mul continuous_const).pow k).div_const _
      exact hpoly.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp_aestronglyMeasurable hf.1)
    have hS_bound : ∀ N : ℕ, ∀ᵐ g ∂(γ n), ‖S N g‖ ≤ bound g := by
      intro N
      refine ae_of_all _ fun g => ?_
      dsimp only [S, bound]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      calc ‖∑ k ∈ Finset.range N, ((inner ℝ g t : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)‖
          ≤ ∑ k ∈ Finset.range N, ‖((inner ℝ g t : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)‖ :=
            norm_sum_le _ _
        _ = ∑ k ∈ Finset.range N, |inner ℝ g t| ^ k / (k.factorial : ℝ) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            simp [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ Real.exp |inner ℝ g t| := Real.sum_le_exp_of_nonneg (abs_nonneg _) N
    have hS_lim : ∀ᵐ g ∂(γ n), Filter.Tendsto (fun N => S N g) Filter.atTop
        (𝓝 (Complex.exp ((inner ℝ g t : ℂ) * Complex.I) * (f g : ℂ))) := by
      refine ae_of_all _ fun g => ?_
      exact (tendsto_complex_exp_partial_sums ((inner ℝ g t : ℂ) * Complex.I)).mul_const (f g : ℂ)
    have hS_int : ∀ N : ℕ, ∫ g : E n, S N g ∂(γ n) = 0 := by
      intro N
      have hdecomp : ∀ g : E n, S N g = ∑ k ∈ Finset.range N,
          (Complex.I ^ k / (k.factorial : ℂ)) * (((inner ℝ g t) ^ k * f g : ℝ) : ℂ) := by
        intro g
        dsimp only [S]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        push_cast [mul_pow]
        ring
      simp_rw [hdecomp]
      have hk_int : ∀ k : ℕ, Integrable (fun g : E n =>
          (Complex.I ^ k / (k.factorial : ℂ)) * (((inner ℝ g t) ^ k * f g : ℝ) : ℂ)) (γ n) := by
        intro k
        have hr := (integral_P_Hnd_mul_eq_zero hf h0 (inner_pow_mem_P_Hnd (k := k) t)).1
        exact (hr.ofReal).const_mul _
      rw [integral_finsetSum _ fun k _ => hk_int k]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [integral_const_mul, integral_complex_ofReal,
        (integral_P_Hnd_mul_eq_zero hf h0 (inner_pow_mem_P_Hnd (k := k) t)).2]
      simp
    have htend := MeasureTheory.tendsto_integral_of_dominated_convergence bound hS_meas hbound_int
      hS_bound hS_lim
    have htend0 : Filter.Tendsto (fun N => ∫ g : E n, S N g ∂(γ n)) Filter.atTop (𝓝 0) := by
      simp_rw [hS_int]; exact tendsto_const_nhds
    exact tendsto_nhds_unique htend htend0
  have hf_int : Integrable f (γ n) := hf.integrable one_le_two
  let f' : E n → ℝ := hf.aestronglyMeasurable.mk f
  have hf'_meas : Measurable f' := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hf'_ae : f =ᵐ[γ n] f' := hf.aestronglyMeasurable.ae_eq_mk
  let fp : E n → ℝ := fun g => max (f' g) 0
  let fm : E n → ℝ := fun g => max (-f' g) 0
  have hfp_meas : Measurable fp := hf'_meas.max measurable_const
  have hfm_meas : Measurable fm := hf'_meas.neg.max measurable_const
  have hfp_int : Integrable fp (γ n) := by
    have hf'_int : Integrable f' (γ n) := hf_int.congr hf'_ae
    exact (hf'_int.abs).mono' hfp_meas.aestronglyMeasurable (ae_of_all _ fun g => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _) (abs_nonneg _))
  have hfm_int : Integrable fm (γ n) := by
    have hf'_int : Integrable f' (γ n) := hf_int.congr hf'_ae
    exact (hf'_int.abs).mono' hfm_meas.aestronglyMeasurable (ae_of_all _ fun g => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (neg_le_abs _) (abs_nonneg _))
  let μp : Measure (E n) := (γ n).withDensity (fun g => ENNReal.ofReal (fp g))
  let μm : Measure (E n) := (γ n).withDensity (fun g => ENNReal.ofReal (fm g))
  have : IsFiniteMeasure μp := isFiniteMeasure_withDensity (by
    rw [← ofReal_integral_eq_lintegral_ofReal hfp_int (ae_of_all _ fun g => le_max_right _ _)]
    exact ENNReal.ofReal_ne_top)
  have : IsFiniteMeasure μm := isFiniteMeasure_withDensity (by
    rw [← ofReal_integral_eq_lintegral_ofReal hfm_int (ae_of_all _ fun g => le_max_right _ _)]
    exact ENNReal.ofReal_ne_top)
  have hμeq : μp = μm := by
    apply MeasureTheory.Measure.ext_of_charFun
    ext t
    have hcf : ∀ (h : E n → ℝ), Measurable h → (∀ g, 0 ≤ h g) → Integrable h (γ n) →
        MeasureTheory.charFun ((γ n).withDensity (fun g => ENNReal.ofReal (h g))) t =
          ∫ g : E n, Complex.exp ((inner ℝ g t : ℂ) * Complex.I) * (h g : ℂ) ∂(γ n) := by
      intro h hh_meas hh_nn _
      rw [MeasureTheory.charFun_apply,
        integral_withDensity_eq_integral_toReal_smul hh_meas.ennreal_ofReal
          (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      refine integral_congr_ae (ae_of_all _ fun g => ?_)
      dsimp only
      rw [ENNReal.toReal_ofReal (hh_nn g), Complex.real_smul, mul_comm]
    rw [hcf fp hfp_meas (fun _ => le_max_right _ _) hfp_int,
      hcf fm hfm_meas (fun _ => le_max_right _ _) hfm_int]
    rw [← sub_eq_zero]
    have hsub_eq : (fun g : E n =>
          Complex.exp ((inner ℝ g t : ℂ) * Complex.I) * (fp g : ℂ) -
            Complex.exp ((inner ℝ g t : ℂ) * Complex.I) * (fm g : ℂ)) =ᵐ[γ n]
        fun g => Complex.exp ((inner ℝ g t : ℂ) * Complex.I) * (f g : ℂ) := by
      filter_upwards [hf'_ae] with g hg
      have hfpm : fp g - fm g = f' g := by
        dsimp only [fp, fm]
        rcases le_total (f' g) 0 with h | h
        · have h2 : 0 ≤ -f' g := neg_nonneg.mpr h
          simp [max_eq_right h, max_eq_left h2]
        · have h2 : -f' g ≤ 0 := neg_nonpos.mpr h
          simp [max_eq_left h, max_eq_right h2]
      rw [← mul_sub, ← Complex.ofReal_sub, hfpm, ← hg]
    have hc_int : ∀ (h : E n → ℝ), Measurable h → Integrable h (γ n) →
        Integrable (fun g : E n =>
          Complex.exp ((inner ℝ g t : ℂ) * Complex.I) * (h g : ℂ)) (γ n) := by
      intro h hh_meas hh_int
      refine hh_int.norm.mono' ?_ (ae_of_all _ fun g => ?_)
      · exact ((Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
            (continuous_id.inner continuous_const)).mul continuous_const)).aestronglyMeasurable).mul
            (Complex.continuous_ofReal.comp_aestronglyMeasurable hh_meas.aestronglyMeasurable)
      · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real]
    have hp_c := hc_int fp hfp_meas hfp_int
    have hm_c := hc_int fm hfm_meas hfm_int
    rw [← integral_sub hp_c hm_c, integral_congr_ae hsub_eq, hchar_int t]
  let Ap : Set (E n) := {g : E n | 0 < f' g}
  let Am : Set (E n) := {g : E n | f' g < 0}
  have hAp_meas : MeasurableSet Ap := measurableSet_lt measurable_const hf'_meas
  have hAm_meas : MeasurableSet Am := measurableSet_lt hf'_meas measurable_const
  have hμp_Ap : μp Ap = 0 := by
    have hμm_Ap : μm Ap = 0 := by
      rw [withDensity_apply _ hAp_meas, lintegral_eq_zero_iff' hfm_meas.ennreal_ofReal.aemeasurable.restrict,
        EventuallyEq, ae_restrict_iff' hAp_meas]
      refine ae_of_all _ fun g hg => ?_
      have hfm0 : fm g ≤ 0 := max_le (by linarith [Set.mem_ofPred_eq.mp hg]) le_rfl
      exact ENNReal.ofReal_eq_zero.mpr hfm0
    have h := congrArg (fun ν : Measure (E n) => ν Ap) hμeq
    exact h.trans hμm_Ap
  have hμm_Am : μm Am = 0 := by
    have hμp_Am : μp Am = 0 := by
      rw [withDensity_apply _ hAm_meas, lintegral_eq_zero_iff' hfp_meas.ennreal_ofReal.aemeasurable.restrict,
        EventuallyEq, ae_restrict_iff' hAm_meas]
      refine ae_of_all _ fun g hg => ?_
      have hfp0 : fp g ≤ 0 := max_le (by linarith [Set.mem_ofPred_eq.mp hg]) le_rfl
      exact ENNReal.ofReal_eq_zero.mpr hfp0
    have h := congrArg (fun ν : Measure (E n) => ν Am) hμeq.symm
    exact h.trans hμp_Am
  have hae_nonpos : ∀ᵐ g ∂(γ n), f' g ≤ 0 := by
    rw [withDensity_apply _ hAp_meas, lintegral_eq_zero_iff' hfp_meas.ennreal_ofReal.aemeasurable.restrict,
      EventuallyEq, ae_restrict_iff' hAp_meas] at hμp_Ap
    filter_upwards [hμp_Ap] with g hg
    by_contra hlt
    push Not at hlt
    have hlt' : 0 < f' g := hlt
    have h0 := hg hlt'
    have hpos : 0 < fp g := lt_of_lt_of_le hlt' (le_max_left _ _)
    rw [Pi.zero_apply, ENNReal.ofReal_eq_zero] at h0
    linarith
  have hae_nonneg : ∀ᵐ g ∂(γ n), 0 ≤ f' g := by
    rw [withDensity_apply _ hAm_meas, lintegral_eq_zero_iff' hfm_meas.ennreal_ofReal.aemeasurable.restrict,
      EventuallyEq, ae_restrict_iff' hAm_meas] at hμm_Am
    filter_upwards [hμm_Am] with g hg
    by_contra hlt
    push Not at hlt
    have hlt' : f' g < 0 := hlt
    have h0 := hg hlt'
    have hpos : 0 < fm g := lt_of_lt_of_le (neg_pos.mpr hlt') (le_max_left _ _)
    rw [Pi.zero_apply, ENNReal.ofReal_eq_zero] at h0
    linarith
  filter_upwards [hf'_ae, hae_nonpos, hae_nonneg] with g hg h1 h2
  rw [hg, Pi.zero_apply]; linarith

/-! ### Hilbert Basis, Parseval, and Infinite 1D Bound -/

noncomputable def HndL2 {n : ℕ} (α : Fin n → ℕ) : Lp ℝ 2 (γ n) :=
  (memLp_Hnd α).toLp (Hnd α)

lemma HndL2_coeFn {n : ℕ} (α : Fin n → ℕ) : (HndL2 α : E n → ℝ) =ᵐ[γ n] Hnd α :=
  (memLp_Hnd α).coeFn_toLp

lemma orthonormal_HndL2 (n : ℕ) : Orthonormal ℝ (HndL2 : (Fin n → ℕ) → Lp ℝ 2 (γ n)) := by
  rw [orthonormal_iff_ite]
  intro α β
  rw [MeasureTheory.L2.inner_def]
  have hae : (fun g : E n => inner ℝ (HndL2 α g) (HndL2 β g)) =ᵐ[γ n]
      fun g => Hnd α g * Hnd β g := by
    filter_upwards [HndL2_coeFn α, HndL2_coeFn β] with g h1 h2
    simp only [h1, h2, RCLike.inner_apply, conj_trivial, mul_comm]
  rw [integral_congr_ae hae, Hnd_orthonormal]

lemma dense_span_HndL2 (n : ℕ) :
    ⊤ ≤ (Submodule.span ℝ (Set.range (HndL2 : (Fin n → ℕ) → Lp ℝ 2 (γ n)))).topologicalClosure := by
  let K := (Submodule.span ℝ (Set.range (HndL2 : (Fin n → ℕ) → Lp ℝ 2 (γ n)))).topologicalClosure
  have hcl : IsClosed (K : Set (Lp ℝ 2 (γ n))) := Submodule.isClosed_topologicalClosure _
  have : CompleteSpace K := hcl.completeSpace_coe
  have hbot : Kᗮ = ⊥ := by
    rw [eq_bot_iff]
    intro F hF
    have hK_le : Submodule.span ℝ (Set.range (HndL2 : (Fin n → ℕ) → Lp ℝ 2 (γ n))) ≤ K :=
      Submodule.le_topologicalClosure _
    have hF_orth : F ∈ (Submodule.span ℝ (Set.range (HndL2 : (Fin n → ℕ) → Lp ℝ 2 (γ n))))ᗮ :=
      Submodule.orthogonal_le hK_le hF
    have h0 : ∀ α : Fin n → ℕ, ∫ g : E n, Hnd α g * (F : E n → ℝ) g ∂(γ n) = 0 := by
      intro α
      have hin := (Submodule.mem_orthogonal _ F).mp hF_orth (HndL2 α) (Submodule.subset_span ⟨α, rfl⟩)
      rw [MeasureTheory.L2.inner_def] at hin
      have hae : (fun g : E n => Hnd α g * (F : E n → ℝ) g) =ᵐ[γ n]
          fun g => inner ℝ (HndL2 α g) (F g) := by
        filter_upwards [HndL2_coeFn α] with g hg
        simp only [hg, RCLike.inner_apply, conj_trivial, mul_comm]
      rw [integral_congr_ae hae, hin]
    have hae0 : (F : E n → ℝ) =ᵐ[γ n] 0 := integral_Hnd_mul_eq_zero_imp (Lp.memLp F) h0
    rw [Submodule.mem_bot]
    exact Lp.ext (hae0.trans (Lp.coeFn_zero ℝ 2 (γ n)).symm)
  exact (Submodule.orthogonal_eq_bot_iff.mp hbot).ge

noncomputable def hermiteHB (n : ℕ) : HilbertBasis (Fin n → ℕ) ℝ (Lp ℝ 2 (γ n)) :=
  HilbertBasis.mk (orthonormal_HndL2 n) (dense_span_HndL2 n)

noncomputable def coeff_nd {n : ℕ} (f : E n → ℝ) (α : Fin n → ℕ) : ℝ :=
  ∫ g : E n, Hnd α g * f g ∂(γ n)

lemma hermiteHB_repr_eq {n : ℕ} {f : E n → ℝ} (hf : MemLp f 2 (γ n)) (α : Fin n → ℕ) :
    (hermiteHB n).repr (hf.toLp f) α = coeff_nd f α := by
  rw [HilbertBasis.repr_apply_apply, hermiteHB, HilbertBasis.coe_mk, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [HndL2_coeFn α, hf.coeFn_toLp] with g h1 h2
  simp only [h1, h2, RCLike.inner_apply, conj_trivial, mul_comm]

lemma parseval_nd {n : ℕ} {f : E n → ℝ} (hf : MemLp f 2 (γ n)) :
    HasSum (fun α : Fin n → ℕ => (coeff_nd f α) ^ 2) (∫ g : E n, (f g) ^ 2 ∂(γ n)) := by
  let F := hf.toLp f
  have hts := (hermiteHB n).hasSum_inner_mul_inner F F
  have hterm : (fun α : Fin n → ℕ => inner ℝ F (hermiteHB n α) * inner ℝ (hermiteHB n α) F) =
      fun α => (coeff_nd f α) ^ 2 := by
    ext α
    have h1 : inner ℝ (hermiteHB n α) F = coeff_nd f α := by
      rw [← (hermiteHB n).repr_apply_apply F α, hermiteHB_repr_eq hf α]
    have h2 : inner ℝ F (hermiteHB n α) = coeff_nd f α := by
      rw [real_inner_comm, h1]
    rw [h1, h2, sq]
  have hnorm : inner ℝ F F = ∫ g : E n, (f g) ^ 2 ∂(γ n) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with g hg
    dsimp only [F]
    rw [hg]
    simp only [RCLike.inner_apply, conj_trivial, sq]
  rwa [hterm, hnorm] at hts

noncomputable def e1Equiv : E 1 ≃ₗᵢ[ℝ] ℝ where
  toFun g := g 0
  invFun x := WithLp.toLp 2 (fun _ => x)
  left_inv g := by ext i; fin_cases i; rfl
  right_inv x := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' g := by
    have h : ‖g‖ ^ 2 = (g 0) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]; simp
    have h0 : |g 0| = ‖g‖ := by
      rw [← Real.sqrt_sq (norm_nonneg g), h, Real.sqrt_sq_eq_abs]
    rw [Real.norm_eq_abs]
    exact h0

lemma measurePreserving_e1 : MeasurePreserving e1Equiv (γ 1) (ProbabilityTheory.gaussianReal 0 1) := by
  refine ⟨e1Equiv.continuous.measurable, ?_⟩
  have hcomp : (e1Equiv : E 1 → ℝ) ∘ (WithLp.toLp 2 : (Fin 1 → ℝ) → E 1) =
      ⇑(MeasurableEquiv.funUnique (Fin 1) ℝ) := rfl
  rw [γ, ← ProbabilityTheory.map_pi_eq_stdGaussian,
    Measure.map_map e1Equiv.continuous.measurable
      (PiLp.lipschitzWith_toLp 2 (fun _ : Fin 1 => ℝ)).continuous.measurable,
    hcomp]
  exact (MeasureTheory.measurePreserving_funUnique (ProbabilityTheory.gaussianReal 0 1) (Fin 1)).map_eq

lemma W1D_sgn_mul (m : ℕ) {f : ℝ → ℝ} (hf : MemLp f 2 (ProbabilityTheory.gaussianReal 0 1)) :
    ∑' j : ℕ, ENNReal.ofReal ((j + m + 1 : ℝ) ^ (1 / 4 : ℝ) *
        (∫ x, h1D j x * ((sgn x : ℝ) * f x) ∂(ProbabilityTheory.gaussianReal 0 1)) ^ 2) ≤
      4402 * ∑' k : ℕ, ENNReal.ofReal ((k + m + 1 : ℝ) ^ (1 / 4 : ℝ) *
        (∫ x, h1D k x * f x ∂(ProbabilityTheory.gaussianReal 0 1)) ^ 2) := by
  let γ1 := ProbabilityTheory.gaussianReal 0 1
  let b : ℕ → ℝ := fun k => ∫ x, h1D k x * f x ∂γ1
  let c : ℕ → ℝ := fun j => ∫ x, h1D j x * ((sgn x : ℝ) * f x) ∂γ1
  have hsgn_meas : Measurable (fun x : ℝ => (sgn x : ℝ)) :=
    measurable_from_top.comp (Measurable.ite measurableSet_Ici measurable_const measurable_const)
  let αOf : ℕ ≃ (Fin 1 → ℕ) :=
    { toFun := fun k _ => k
      invFun := fun α => α 0
      left_inv := fun _ => rfl
      right_inv := fun α => by ext i; fin_cases i; rfl }
  have hHnd_e1 : ∀ k : ℕ, ∀ g : E 1, Hnd (αOf k) g = h1D k (e1Equiv g) := by
    intro k g; simp [Hnd, αOf]; rfl
  let f1 : E 1 → ℝ := fun g => f (e1Equiv g)
  have hf1 : MemLp f1 2 (γ 1) :=
    hf.comp_measurePreserving measurePreserving_e1
  let F1 : Lp ℝ 2 (γ 1) := hf1.toLp f1
  have hmp_e1_homeo : MeasurePreserving e1Equiv.toHomeomorph (γ 1) (ProbabilityTheory.gaussianReal 0 1) :=
    measurePreserving_e1
  have hb_eq : ∀ k : ℕ, (hermiteHB 1).repr F1 (αOf k) = b k := by
    intro k
    rw [hermiteHB_repr_eq hf1 (αOf k), coeff_nd]
    calc ∫ g : E 1, Hnd (αOf k) g * f1 g ∂(γ 1)
        = ∫ g : E 1, (fun x => h1D k x * f x) (e1Equiv.toHomeomorph g) ∂(γ 1) := by
          refine integral_congr_ae (ae_of_all _ fun g => ?_)
          dsimp only; rw [hHnd_e1 k]; rfl
      _ = b k := hmp_e1_homeo.integral_comp e1Equiv.toHomeomorph.measurableEmbedding
          (fun x => h1D k x * f x)
  have hhasSum : HasSum (fun k : ℕ => b k • (hermiteHB 1) (αOf k)) F1 := by
    have hrew : (fun k : ℕ => b k • (hermiteHB 1) (αOf k)) =
        (fun α : Fin 1 → ℕ => (hermiteHB 1).repr F1 α • (hermiteHB 1) α) ∘ αOf := by
      ext k; simp [hb_eq]
    rw [hrew, αOf.hasSum_iff]
    exact (hermiteHB 1).hasSum_repr F1
  have htend_F : Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, b k • (hermiteHB 1) (αOf k))
      Filter.atTop (𝓝 F1) := hhasSum.tendsto_sum_nat
  have hPN_ae : ∀ M : ℕ,
      ((∑ k ∈ Finset.range M, b k • (hermiteHB 1) (αOf k) : Lp ℝ 2 (γ 1)) : E 1 → ℝ) =ᵐ[γ 1]
        fun g => ∑ k ∈ Finset.range M, b k * Hnd (αOf k) g := by
    intro M
    induction M with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact Lp.coeFn_zero ℝ 2 (γ 1)
    | succ M ih =>
      have hadd : (∑ k ∈ Finset.range (M + 1), b k • (hermiteHB 1) (αOf k)) =
          (∑ k ∈ Finset.range M, b k • (hermiteHB 1) (αOf k)) + b M • (hermiteHB 1) (αOf M) :=
        Finset.sum_range_succ _ M
      rw [hadd]
      have hlast : ((b M • (hermiteHB 1) (αOf M) : Lp ℝ 2 (γ 1)) : E 1 → ℝ) =ᵐ[γ 1]
          fun g => b M * Hnd (αOf M) g := by
        have h1 := Lp.coeFn_smul (b M) ((hermiteHB 1) (αOf M))
        have h2 : (((hermiteHB 1) (αOf M) : Lp ℝ 2 (γ 1)) : E 1 → ℝ) =ᵐ[γ 1] Hnd (αOf M) := by
          rw [hermiteHB, HilbertBasis.coe_mk]
          exact HndL2_coeFn (αOf M)
        filter_upwards [h1, h2] with g hg1 hg2
        rw [hg1, Pi.smul_apply, smul_eq_mul, hg2]
      filter_upwards [Lp.coeFn_add (∑ k ∈ Finset.range M, b k • (hermiteHB 1) (αOf k))
        (b M • (hermiteHB 1) (αOf M)), ih, hlast] with g ha hb hc
      rw [ha, Pi.add_apply, hb, hc, Finset.sum_range_succ]
  have htend_c : ∀ j : ℕ, Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, M j k * b k)
      Filter.atTop (𝓝 (c j)) := by
    intro j
    have hdiff_tend : Filter.Tendsto
        (fun N : ℕ => (∑ k ∈ Finset.range N, M j k * b k) - c j) Filter.atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hnorm_tend : Filter.Tendsto
          (fun N : ℕ => ‖(∑ k ∈ Finset.range N, b k • (hermiteHB 1) (αOf k)) - F1‖)
          Filter.atTop (𝓝 0) := by
        rw [← tendsto_iff_norm_sub_tendsto_zero]
        exact htend_F
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hnorm_tend
        (fun _ => norm_nonneg _) (fun N => ?_)
      let PN : Lp ℝ 2 (γ 1) := ∑ k ∈ Finset.range N, b k • (hermiteHB 1) (αOf k)
      let diff : E 1 → ℝ := fun g => (sgn (e1Equiv g) : ℝ) * ((PN : E 1 → ℝ) g - (F1 : E 1 → ℝ) g)
      have hdiff_memLp : MemLp diff 2 (γ 1) := by
        have hsm : AEStronglyMeasurable diff (γ 1) :=
          (hsgn_meas.comp e1Equiv.continuous.measurable).aestronglyMeasurable.mul
            ((Lp.memLp (PN - F1)).1.congr (Lp.coeFn_sub PN F1))
        refine MemLp.of_le_mul (Lp.memLp (PN - F1)) (c := 1) hsm ?_
        filter_upwards [Lp.coeFn_sub PN F1] with g hg
        have habs_sgn : |(sgn (e1Equiv g) : ℝ)| = 1 := by simp only [sgn]; split_ifs <;> norm_num
        rw [one_mul, Real.norm_eq_abs, abs_mul, habs_sgn, one_mul, hg, Pi.sub_apply, Real.norm_eq_abs]
      let G : Lp ℝ 2 (γ 1) := hdiff_memLp.toLp diff
      have hG_norm : ‖G‖ ≤ ‖PN - F1‖ := by
        have hsq : ‖G‖ ^ 2 ≤ ‖PN - F1‖ ^ 2 := by
          rw [← real_inner_self_eq_norm_sq G, ← real_inner_self_eq_norm_sq (PN - F1),
            MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
          refine le_of_eq (integral_congr_ae ?_)
          filter_upwards [hdiff_memLp.coeFn_toLp, Lp.coeFn_sub PN F1] with g hg1 hg2
          have hsgn2 : (sgn (e1Equiv g) : ℝ) ^ 2 = 1 := by simp only [sgn]; split_ifs <;> norm_num
          rw [hg1, hg2]
          simp only [diff, Pi.sub_apply, RCLike.inner_apply, conj_trivial]
          calc ((sgn (e1Equiv g) : ℝ) * ((PN : E 1 → ℝ) g - (F1 : E 1 → ℝ) g)) *
                ((sgn (e1Equiv g) : ℝ) * ((PN : E 1 → ℝ) g - (F1 : E 1 → ℝ) g))
              = (sgn (e1Equiv g) : ℝ) ^ 2 *
                  (((PN : E 1 → ℝ) g - (F1 : E 1 → ℝ) g) * ((PN : E 1 → ℝ) g - (F1 : E 1 → ℝ) g)) := by ring
            _ = ((PN : E 1 → ℝ) g - (F1 : E 1 → ℝ) g) * ((PN : E 1 → ℝ) g - (F1 : E 1 → ℝ) g) := by
                rw [hsgn2, one_mul]
        nlinarith [norm_nonneg G, norm_nonneg (PN - F1)]
      have hinner_eq : inner ℝ (HndL2 (αOf j)) G = (∑ k ∈ Finset.range N, M j k * b k) - c j := by
        rw [MeasureTheory.L2.inner_def]
        have hae : (fun g : E 1 => inner ℝ (HndL2 (αOf j) g) (G g)) =ᵐ[γ 1]
            fun g => (∑ k ∈ Finset.range N, b k * ((sgn (e1Equiv g) : ℝ) * Hnd (αOf j) g * Hnd (αOf k) g)) -
              Hnd (αOf j) g * ((sgn (e1Equiv g) : ℝ) * f1 g) := by
          filter_upwards [HndL2_coeFn (αOf j), hdiff_memLp.coeFn_toLp, hPN_ae N, hf1.coeFn_toLp] with
            g hj hg hpn hf1g
          rw [hj, hg]
          simp only [diff, RCLike.inner_apply, conj_trivial]
          rw [hpn, hf1g]
          simp only [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul]
          refine congrArg₂ (· - ·) (Finset.sum_congr rfl fun k _ => by ring) (by ring)
        rw [integral_congr_ae hae]
        have hk_int : ∀ k : ℕ, Integrable (fun g : E 1 =>
            b k * ((sgn (e1Equiv g) : ℝ) * Hnd (αOf j) g * Hnd (αOf k) g)) (γ 1) := by
          intro k
          have hsgn_j : MemLp (fun g : E 1 => (sgn (e1Equiv g) : ℝ) * Hnd (αOf j) g) 2 (γ 1) := by
            have hsm : AEStronglyMeasurable (fun g : E 1 => (sgn (e1Equiv g) : ℝ) * Hnd (αOf j) g) (γ 1) :=
              (hsgn_meas.comp e1Equiv.continuous.measurable).aestronglyMeasurable.mul
                (continuous_Hnd (αOf j)).aestronglyMeasurable
            refine (memLp_Hnd (αOf j)).of_le_mul (c := 1) hsm (ae_of_all _ fun g => ?_)
            have habs_sgn : |(sgn (e1Equiv g) : ℝ)| = 1 := by simp only [sgn]; split_ifs <;> norm_num
            rw [one_mul, Real.norm_eq_abs, abs_mul, habs_sgn, one_mul, Real.norm_eq_abs]
          have heq : (fun g : E 1 => b k * ((sgn (e1Equiv g) : ℝ) * Hnd (αOf j) g * Hnd (αOf k) g)) =
              fun g => b k * (((sgn (e1Equiv g) : ℝ) * Hnd (αOf j) g) * Hnd (αOf k) g) := by
            ext g; ring
          rw [heq]
          exact (integrable_mul_of_memLp_two hsgn_j (memLp_Hnd (αOf k))).const_mul _
        have hint_sum : Integrable (fun g : E 1 => ∑ k ∈ Finset.range N,
            b k * ((sgn (e1Equiv g) : ℝ) * Hnd (αOf j) g * Hnd (αOf k) g)) (γ 1) :=
          integrable_finsetSum _ fun k _ => hk_int k
        have hint_c : Integrable (fun g : E 1 => Hnd (αOf j) g * ((sgn (e1Equiv g) : ℝ) * f1 g)) (γ 1) := by
          have hsgn_f1 : MemLp (fun g : E 1 => (sgn (e1Equiv g) : ℝ) * f1 g) 2 (γ 1) := by
            have hsm : AEStronglyMeasurable (fun g : E 1 => (sgn (e1Equiv g) : ℝ) * f1 g) (γ 1) :=
              (hsgn_meas.comp e1Equiv.continuous.measurable).aestronglyMeasurable.mul hf1.1
            refine hf1.of_le_mul (c := 1) hsm (ae_of_all _ fun g => ?_)
            have habs_sgn : |(sgn (e1Equiv g) : ℝ)| = 1 := by simp only [sgn]; split_ifs <;> norm_num
            rw [one_mul, Real.norm_eq_abs, abs_mul, habs_sgn, one_mul, Real.norm_eq_abs]
          exact integrable_mul_of_memLp_two (memLp_Hnd (αOf j)) hsgn_f1
        rw [integral_sub hint_sum hint_c, integral_finsetSum _ fun k _ => hk_int k]
        have hterm : ∀ k : ℕ, ∫ g : E 1,
            b k * ((sgn (e1Equiv g) : ℝ) * Hnd (αOf j) g * Hnd (αOf k) g) ∂(γ 1) = M j k * b k := by
          intro k
          rw [integral_const_mul]
          have hI : ∫ g : E 1, (sgn (e1Equiv g) : ℝ) * Hnd (αOf j) g * Hnd (αOf k) g ∂(γ 1) = M j k := by
            calc ∫ g : E 1, (sgn (e1Equiv g) : ℝ) * Hnd (αOf j) g * Hnd (αOf k) g ∂(γ 1)
                = ∫ g : E 1, (fun x : ℝ => (sgn x : ℝ) * h1D j x * h1D k x) (e1Equiv.toHomeomorph g) ∂(γ 1) := by
                  refine integral_congr_ae (ae_of_all _ fun g => ?_)
                  dsimp only; simp [hHnd_e1]
              _ = M j k := hmp_e1_homeo.integral_comp e1Equiv.toHomeomorph.measurableEmbedding
                  (fun x : ℝ => (sgn x : ℝ) * h1D j x * h1D k x)
          rw [hI, mul_comm]
        have hc_eq : ∫ g : E 1, Hnd (αOf j) g * ((sgn (e1Equiv g) : ℝ) * f1 g) ∂(γ 1) = c j := by
          calc ∫ g : E 1, Hnd (αOf j) g * ((sgn (e1Equiv g) : ℝ) * f1 g) ∂(γ 1)
              = ∫ g : E 1, (fun x : ℝ => h1D j x * ((sgn x : ℝ) * f x)) (e1Equiv.toHomeomorph g) ∂(γ 1) := by
                refine integral_congr_ae (ae_of_all _ fun g => ?_)
                dsimp only; simp [hHnd_e1, f1]
            _ = c j := hmp_e1_homeo.integral_comp e1Equiv.toHomeomorph.measurableEmbedding
                (fun x : ℝ => h1D j x * ((sgn x : ℝ) * f x))
        rw [hc_eq]
        congr 1
        exact Finset.sum_congr rfl fun k _ => hterm k
      have hcs : ‖(∑ k ∈ Finset.range N, M j k * b k) - c j‖ ≤ ‖HndL2 (αOf j)‖ * ‖G‖ := by
        rw [← hinner_eq]
        exact norm_inner_le_norm _ _
      have hunit : ‖HndL2 (αOf j)‖ = 1 := (orthonormal_HndL2 1).1 (αOf j)
      rw [hunit, one_mul] at hcs
      exact hcs.trans hG_norm
    have hadd := hdiff_tend.add (tendsto_const_nhds (x := c j))
    simpa using hadd
  have hfin_bound : ∀ J : ℕ,
      ∑ j ∈ Finset.range J, ENNReal.ofReal ((j + m + 1 : ℝ) ^ (1 / 4 : ℝ) * (c j) ^ 2) ≤
        4402 * ∑' k : ℕ, ENNReal.ofReal ((k + m + 1 : ℝ) ^ (1 / 4 : ℝ) * (b k) ^ 2) := by
    intro J
    have htend_sum : Filter.Tendsto (fun N : ℕ =>
        ∑ j ∈ Finset.range J, ENNReal.ofReal ((j + m + 1 : ℝ) ^ (1 / 4 : ℝ) *
          (∑ k ∈ Finset.range N, M j k * b k) ^ 2))
        Filter.atTop
        (𝓝 (∑ j ∈ Finset.range J, ENNReal.ofReal ((j + m + 1 : ℝ) ^ (1 / 4 : ℝ) * (c j) ^ 2))) := by
      refine tendsto_finsetSum _ fun j _ => ?_
      refine ENNReal.continuous_ofReal.continuousAt.tendsto.comp ?_
      exact tendsto_const_nhds.mul ((htend_c j).pow 2)
    refine le_of_tendsto htend_sum ?_
    filter_upwards [Filter.eventually_ge_atTop J] with N hJN
    have hsub : ∑ j ∈ Finset.range J, ENNReal.ofReal ((j + m + 1 : ℝ) ^ (1 / 4 : ℝ) *
          (∑ k ∈ Finset.range N, M j k * b k) ^ 2) ≤
        ∑ j ∈ Finset.range N, ENNReal.ofReal ((j + m + 1 : ℝ) ^ (1 / 4 : ℝ) *
          (∑ k ∈ Finset.range N, M j k * b k) ^ 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hJN) fun _ _ _ => zero_le
    refine hsub.trans ?_
    rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity]
    have hreal := W1D_sgn_mul_fin m N b
    refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_sum_of_nonneg fun k _ => by positivity]
    norm_num
    exact mul_le_mul_of_nonneg_left
      (ENNReal.sum_le_tsum (Finset.range N)) (by positivity)
  rw [ENNReal.tsum_eq_iSup_nat]
  exact iSup_le fun J => hfin_bound J

/-! ### Progress Measure `W_real`, Rotation Invariance, and `n`-Dimensional Lemma 3.4 -/

noncomputable def W_real {n : ℕ} (f : E n → ℝ) : ℝ≥0∞ :=
  ∑' α : Fin n → ℕ, ENNReal.ofReal ((1 + (totalDeg α : ℝ)) ^ (1 / 4 : ℝ) * (coeff_nd f α) ^ 2)

noncomputable def projFin {n : ℕ} (f : E n → ℝ) (d : ℕ) (g : E n) : ℝ :=
  ∑ α ∈ I_deg n d, coeff_nd f α * Hnd α g

lemma projFin_mem_P_Hnd {n : ℕ} (f : E n → ℝ) (d : ℕ) : projFin f d ∈ P_Hnd n d := by
  have heq : projFin f d = ∑ α ∈ I_deg n d, coeff_nd f α • Hnd α := by
    ext g; simp [projFin, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [heq]
  exact Submodule.sum_mem _ fun α hα => Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, hα, rfl⟩)

lemma integral_projFin_orth {n : ℕ} {f : E n → ℝ} (hf : MemLp f 2 (γ n)) (d : ℕ)
    {p : E n → ℝ} (hp : p ∈ P_Hnd n d) :
    ∫ g : E n, p g * (f g - projFin f d g) ∂(γ n) = 0 := by
  have hproj_memLp : MemLp (projFin f d) 2 (γ n) := P_Hnd_memLp (projFin_mem_P_Hnd f d)
  have hsub_memLp : MemLp (fun g => f g - projFin f d g) 2 (γ n) := hf.sub hproj_memLp
  have hgen : ∀ β ∈ I_deg n d, ∫ g : E n, Hnd β g * (f g - projFin f d g) ∂(γ n) = 0 := by
    intro β hβ
    have hmul : ∀ g : E n, Hnd β g * (f g - projFin f d g) =
        Hnd β g * f g - ∑ α ∈ I_deg n d, coeff_nd f α * (Hnd β g * Hnd α g) := by
      intro g
      dsimp only [projFin]
      rw [mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun α _ => by ring
    have hi1 : Integrable (fun g : E n => Hnd β g * f g) (γ n) :=
      integrable_mul_of_memLp_two (memLp_Hnd β) hf
    have hi2 : Integrable (fun g : E n => ∑ α ∈ I_deg n d, coeff_nd f α * (Hnd β g * Hnd α g)) (γ n) :=
      integrable_finsetSum _ fun α _ => (integrable_Hnd_mul_Hnd β α).const_mul _
    simp_rw [hmul]
    rw [integral_sub hi1 hi2, integral_finsetSum _ fun α _ => (integrable_Hnd_mul_Hnd β α).const_mul _]
    simp_rw [integral_const_mul, Hnd_orthonormal]
    rw [Finset.sum_eq_single β]
    · simp [coeff_nd]
    · intro α _ hne; simp [Ne.symm hne]
    · intro hnot; exact absurd hβ hnot
  induction hp using Submodule.span_induction with
  | mem q hq =>
    rcases hq with ⟨β, hβ, rfl⟩
    exact hgen β hβ
  | zero => simp
  | add x y hx hy ihx ihy =>
    have hx1 := integrable_mul_of_memLp_two (P_Hnd_memLp hx) hsub_memLp
    have hy1 := integrable_mul_of_memLp_two (P_Hnd_memLp hy) hsub_memLp
    have hadd : ∀ g : E n, (x + y) g * (f g - projFin f d g) =
        x g * (f g - projFin f d g) + y g * (f g - projFin f d g) := fun g => add_mul _ _ _
    simp_rw [hadd]
    rw [integral_add hx1 hy1, ihx, ihy, add_zero]
  | smul c x _ ihx =>
    have hsm : ∀ g : E n, (c • x) g * (f g - projFin f d g) =
        c * (x g * (f g - projFin f d g)) := fun g => by simp [smul_eq_mul]; ring
    simp_rw [hsm]
    rw [integral_const_mul, ihx, mul_zero]

lemma integral_projFin_sq {n : ℕ} (f : E n → ℝ) (d : ℕ) :
    ∫ g : E n, (projFin f d g) ^ 2 ∂(γ n) = ∑ α ∈ I_deg n d, (coeff_nd f α) ^ 2 := by
  have heq : (fun g : E n => (projFin f d g) ^ 2) =
      fun g => ∑ α ∈ I_deg n d, ∑ β ∈ I_deg n d,
        (coeff_nd f α * coeff_nd f β) * (Hnd α g * Hnd β g) := by
    ext g
    rw [sq, projFin, Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => by ring
  rw [heq, integral_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ =>
    (integrable_Hnd_mul_Hnd α β).const_mul _]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [integral_finsetSum _ fun β _ => (integrable_Hnd_mul_Hnd α β).const_mul _]
  simp_rw [integral_const_mul, Hnd_orthonormal]
  simp [hα, sq]

lemma measurePreserving_isom_γ {n : ℕ} (R : E n ≃ₗᵢ[ℝ] E n) :
    MeasurePreserving R (γ n) (γ n) :=
  ⟨R.continuous.measurable, ProbabilityTheory.stdGaussian_map R⟩

lemma P_Hnd_comp_isom {n d : ℕ} (R : E n ≃ₗᵢ[ℝ] E n) {p : E n → ℝ} (hp : p ∈ P_Hnd n d) :
    (p ∘ R) ∈ P_Hnd n d := by
  induction hp using Submodule.span_induction with
  | mem q hq =>
    rcases hq with ⟨α, hα, rfl⟩
    exact P_Hnd_mono (mem_I_deg.mp hα) (Hnd_comp_isom_mem_P_Hnd α R)
  | zero => exact (P_Hnd n d).zero_mem
  | add x y _ _ ihx ihy =>
    have hadd : ((x + y) ∘ R) = (x ∘ R) + (y ∘ R) := rfl
    rw [hadd]
    exact (P_Hnd n d).add_mem ihx ihy
  | smul c x _ ihx =>
    have hsm : ((c • x) ∘ R) = c • (x ∘ R) := rfl
    rw [hsm]
    exact (P_Hnd n d).smul_mem c ihx

lemma sum_I_deg_coeff_sq_comp_isom {n : ℕ} (R : E n ≃ₗᵢ[ℝ] E n) {f : E n → ℝ}
    (hf : MemLp f 2 (γ n)) (d : ℕ) :
    ∑ α ∈ I_deg n d, (coeff_nd (f ∘ R) α) ^ 2 = ∑ α ∈ I_deg n d, (coeff_nd f α) ^ 2 := by
  have hmp := measurePreserving_isom_γ R
  have hmp_homeo : MeasurePreserving R.toHomeomorph (γ n) (γ n) := hmp
  have hfR : MemLp (f ∘ R) 2 (γ n) := hf.comp_measurePreserving hmp
  let q : E n → ℝ := fun g => projFin f d (R g) - projFin (f ∘ R) d g
  have hq_mem : q ∈ P_Hnd n d :=
    (P_Hnd n d).sub_mem (P_Hnd_comp_isom R (projFin_mem_P_Hnd f d)) (projFin_mem_P_Hnd (f ∘ R) d)
  have hq_orth : ∀ p ∈ P_Hnd n d, ∫ g : E n, p g * q g ∂(γ n) = 0 := by
    intro p hp
    have h1 := integral_projFin_orth hfR d hp
    have hp_symm : (p ∘ R.symm) ∈ P_Hnd n d := P_Hnd_comp_isom R.symm hp
    have h2 := integral_projFin_orth hf d hp_symm
    have h2' : ∫ g : E n, p g * (f (R g) - projFin f d (R g)) ∂(γ n) = 0 := by
      calc ∫ g : E n, p g * (f (R g) - projFin f d (R g)) ∂(γ n)
          = ∫ g : E n, (fun y : E n => (p ∘ R.symm) y * (f y - projFin f d y))
              (R.toHomeomorph g) ∂(γ n) := by
            refine integral_congr_ae (ae_of_all _ fun g => by simp)
        _ = ∫ y : E n, (p ∘ R.symm) y * (f y - projFin f d y) ∂(γ n) :=
            hmp_homeo.integral_comp R.toHomeomorph.measurableEmbedding
              (fun y : E n => (p ∘ R.symm) y * (f y - projFin f d y))
        _ = 0 := h2
    have hi1 : Integrable (fun g : E n => p g * ((f ∘ R) g - projFin (f ∘ R) d g)) (γ n) :=
      integrable_mul_of_memLp_two (P_Hnd_memLp hp) (hfR.sub (P_Hnd_memLp (projFin_mem_P_Hnd _ d)))
    have hi2 : Integrable (fun g : E n => p g * (f (R g) - projFin f d (R g))) (γ n) := by
      have hm : MemLp (fun g => f (R g) - projFin f d (R g)) 2 (γ n) :=
        hfR.sub (P_Hnd_memLp (P_Hnd_comp_isom R (projFin_mem_P_Hnd f d)))
      exact integrable_mul_of_memLp_two (P_Hnd_memLp hp) hm
    have hsub : ∀ g : E n, p g * q g =
        p g * ((f ∘ R) g - projFin (f ∘ R) d g) - p g * (f (R g) - projFin f d (R g)) := by
      intro g; dsimp only [q, Function.comp_def]; ring
    simp_rw [hsub]
    rw [integral_sub hi1 hi2, h1, h2', sub_zero]
  have hq0 : ∫ g : E n, (q g) ^ 2 ∂(γ n) = 0 := by
    simpa [sq] using hq_orth q hq_mem
  have hq_sq_int : Integrable (fun g : E n => (q g) ^ 2) (γ n) :=
    (P_Hnd_memLp hq_mem).integrable_sq
  have hae0 : q =ᵐ[γ n] 0 := by
    have h := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun g => sq_nonneg (q g)) hq_sq_int).mp hq0
    filter_upwards [h] with g hg
    exact sq_eq_zero_iff.mp hg
  have hae_eq : (fun g : E n => (projFin (f ∘ R) d g) ^ 2) =ᵐ[γ n]
      fun g => (projFin f d (R g)) ^ 2 := by
    filter_upwards [hae0] with g hg
    have hsub : projFin f d (R g) - projFin (f ∘ R) d g = 0 := hg
    rw [sub_eq_zero.mp hsub]
  calc ∑ α ∈ I_deg n d, (coeff_nd (f ∘ R) α) ^ 2
      = ∫ g : E n, (projFin (f ∘ R) d g) ^ 2 ∂(γ n) := (integral_projFin_sq (f ∘ R) d).symm
    _ = ∫ g : E n, (projFin f d (R.toHomeomorph g)) ^ 2 ∂(γ n) := integral_congr_ae hae_eq
    _ = ∫ y : E n, (projFin f d y) ^ 2 ∂(γ n) :=
        hmp_homeo.integral_comp R.toHomeomorph.measurableEmbedding (fun y => (projFin f d y) ^ 2)
    _ = ∑ α ∈ I_deg n d, (coeff_nd f α) ^ 2 := integral_projFin_sq f d

lemma W_real_comp_isom {n : ℕ} (R : E n ≃ₗᵢ[ℝ] E n) {f : E n → ℝ} (hf : MemLp f 2 (γ n)) :
    W_real (f ∘ R) = W_real f := by
  let layer : (E n → ℝ) → ℕ → ℝ := fun h d => ∑ α ∈ I_deg_eq n d, (coeff_nd h α) ^ 2
  have hW_eq : ∀ h : E n → ℝ,
      W_real h = ∑' d : ℕ, ENNReal.ofReal ((1 + (d : ℝ)) ^ (1 / 4 : ℝ) * layer h d) := by
    intro h
    rw [W_real, ← (Equiv.sigmaFiberEquiv (totalDeg (n := n))).tsum_eq, ENNReal.tsum_sigma']
    refine tsum_congr fun d => ?_
    let e : (I_deg_eq n d) ≃ {α : Fin n → ℕ // totalDeg α = d} :=
      { toFun := fun α => ⟨α.1, mem_I_deg_eq.mp α.2⟩
        invFun := fun α => ⟨α.1, mem_I_deg_eq.mpr α.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← e.tsum_eq, tsum_fintype, Finset.univ_eq_attach]
    have hsum_att : ∑ α ∈ (I_deg_eq n d).attach,
          ENNReal.ofReal ((1 + (totalDeg ((Equiv.sigmaFiberEquiv (totalDeg (n := n))) ⟨d, e α⟩) : ℝ)) ^ (1 / 4 : ℝ) *
            (coeff_nd h ((Equiv.sigmaFiberEquiv (totalDeg (n := n))) ⟨d, e α⟩)) ^ 2) =
        ∑ α ∈ I_deg_eq n d, ENNReal.ofReal ((1 + (d : ℝ)) ^ (1 / 4 : ℝ) * (coeff_nd h α) ^ 2) := by
      rw [← Finset.sum_attach (I_deg_eq n d)]
      refine Finset.sum_congr rfl fun α _ => ?_
      change ENNReal.ofReal ((1 + (totalDeg α.1 : ℝ)) ^ (1 / 4 : ℝ) * (coeff_nd h α.1) ^ 2) = _
      rw [mem_I_deg_eq.mp α.2]
    rw [hsum_att, ← ENNReal.ofReal_sum_of_nonneg fun α _ => by positivity,
      ← Finset.mul_sum]
  have hlayer : ∀ d : ℕ, layer (f ∘ R) d = layer f d := by
    intro d
    cases d with
    | zero =>
      have h0 : I_deg_eq n 0 = I_deg n 0 := by
        ext α; simp [mem_I_deg_eq, mem_I_deg]
      dsimp only [layer]
      rw [h0, sum_I_deg_coeff_sq_comp_isom R hf 0]
    | succ d =>
      have hunion : I_deg n (d + 1) = I_deg n d ∪ I_deg_eq n (d + 1) := by
        ext α
        simp only [Finset.mem_union, mem_I_deg, mem_I_deg_eq]
        omega
      have hdisj : Disjoint (I_deg n d) (I_deg_eq n (d + 1)) := by
        rw [Finset.disjoint_left]
        intro α h1 h2
        rw [mem_I_deg] at h1
        rw [mem_I_deg_eq] at h2
        omega
      have hsum_rel : ∀ h : E n → ℝ,
          ∑ α ∈ I_deg n (d + 1), (coeff_nd h α) ^ 2 =
            (∑ α ∈ I_deg n d, (coeff_nd h α) ^ 2) + layer h (d + 1) := by
        intro h
        dsimp only [layer]
        rw [hunion, Finset.sum_union hdisj]
      have hs1 := sum_I_deg_coeff_sq_comp_isom R hf (d + 1)
      have hs0 := sum_I_deg_coeff_sq_comp_isom R hf d
      rw [hsum_rel (f ∘ R), hsum_rel f] at hs1
      linarith
  rw [hW_eq (f ∘ R), hW_eq f]
  refine tsum_congr fun d => ?_
  rw [hlayer d]

lemma exists_orthonormalBasis_zero {m : ℕ} (u : E (m + 1)) (hu : ‖u‖ = 1) :
    ∃ b : OrthonormalBasis (Fin (m + 1)) ℝ (E (m + 1)), b 0 = u := by
  let U : Submodule ℝ (E (m + 1)) := (Submodule.span ℝ {u})ᗮ
  have hu_ne : u ≠ 0 := by intro h; rw [h, norm_zero] at hu; norm_num at hu
  have hfin_span : Module.finrank ℝ (Submodule.span ℝ {u}) = 1 :=
    finrank_span_singleton hu_ne
  have hfin_total := Submodule.finrank_add_finrank_orthogonal (Submodule.span ℝ {u})
  rw [finrank_euclideanSpace_fin, hfin_span] at hfin_total
  have hfin_U : Module.finrank ℝ U = m := by
    change 1 + Module.finrank ℝ U = m + 1 at hfin_total
    omega
  let bU : OrthonormalBasis (Fin m) ℝ U :=
    (stdOrthonormalBasis ℝ U).reindex (finCongr hfin_U)
  let v : Fin (m + 1) → E (m + 1) := Fin.cons u (fun j => (bU j : E (m + 1)))
  have hv_ortho : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => simp [v, hu]
      | succ j' =>
        have hne : (0 : Fin (m + 1)) ≠ j'.succ := (Fin.succ_ne_zero j').symm
        simp only [v, Fin.cons_zero, Fin.cons_succ, if_neg hne]
        exact (Submodule.mem_orthogonal _ _).mp (bU j').2 u (Submodule.subset_span rfl)
    | succ i' =>
      cases j using Fin.cases with
      | zero =>
        simp only [v, Fin.cons_zero, Fin.cons_succ, Fin.succ_ne_zero, ↓reduceIte]
        rw [real_inner_comm]
        exact (Submodule.mem_orthogonal _ _).mp (bU i').2 u (Submodule.subset_span rfl)
      | succ j' =>
        simp only [v, Fin.cons_succ, Fin.succ_inj]
        exact orthonormal_iff_ite.mp bU.orthonormal i' j'
  have hbot : (Submodule.span ℝ (Set.range v))ᗮ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hmemU : x ∈ U := by
      rw [Submodule.mem_orthogonal]
      intro y hy
      rw [Submodule.mem_span_singleton] at hy
      rcases hy with ⟨c, rfl⟩
      have h0 : inner ℝ u x = 0 := (Submodule.mem_orthogonal _ _).mp hx (v 0)
        (Submodule.subset_span ⟨0, rfl⟩)
      rw [real_inner_smul_left, h0, mul_zero]
    let xU : U := ⟨x, hmemU⟩
    have hxU0 : xU = 0 := by
      rw [← bU.sum_repr xU]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hj : inner ℝ (bU j) xU = 0 := by
        change inner ℝ (bU j : E (m + 1)) x = 0
        exact (Submodule.mem_orthogonal _ _).mp hx (v j.succ) (Submodule.subset_span ⟨j.succ, rfl⟩)
      simp [bU.repr_apply_apply, hj]
    exact congrArg Subtype.val hxU0
  refine ⟨OrthonormalBasis.mkOfOrthogonalEqBot hv_ortho hbot, ?_⟩
  simp [OrthonormalBasis.coe_of_orthogonal_eq_bot_mk, v]

lemma W_real_sgn_inner_mul_le {n : ℕ} {f : E n → ℝ} (hf : MemLp f 2 (γ n))
    (x : E n) (hx : x ≠ 0) :
    W_real (fun g => (sgn (inner ℝ g x) : ℝ) * f g) ≤ 4402 * W_real f := by
  cases n with
  | zero =>
    exact absurd (Subsingleton.elim x 0) hx
  | succ m =>
    let u : E (m + 1) := ‖x‖⁻¹ • x
    have hu : ‖u‖ = 1 := norm_smul_inv_norm hx
    have hsgn_eq : ∀ g : E (m + 1), sgn (inner ℝ g x) = sgn (inner ℝ g u) := by
      intro g
      have hpos : 0 < ‖x‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hx)
      have hmul : inner ℝ g u = ‖x‖⁻¹ * inner ℝ g x := by
        dsimp [u]; rw [real_inner_smul_right]
      simp only [sgn, hmul]
      split_ifs with h1 h2 h2
      · rfl
      · exfalso; exact h2 (mul_nonneg hpos.le h1)
      · exfalso; exact h1 (nonneg_of_mul_nonneg_right h2 hpos)
      · rfl
    have hfun_u : (fun g : E (m + 1) => (sgn (inner ℝ g x) : ℝ) * f g) =
        fun g => (sgn (inner ℝ g u) : ℝ) * f g := by
      ext g; rw [hsgn_eq g]
    rw [hfun_u]
    obtain ⟨b, hb0⟩ := exists_orthonormalBasis_zero u hu
    let R : E (m + 1) ≃ₗᵢ[ℝ] E (m + 1) :=
      (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).equiv b (Equiv.refl _)
    have hR0 : R (EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0) = u := by
      dsimp [R]
      rw [OrthonormalBasis.equiv_apply_basis, Equiv.refl_apply, hb0]
    have hinner_R : ∀ g : E (m + 1), inner ℝ (R g) u = g 0 := by
      intro g
      rw [← hR0, R.inner_map_eq_flip, R.symm_apply_apply, EuclideanSpace.inner_basisFun_real (Fin (m + 1))]
    let f1 : E (m + 1) → ℝ := f ∘ R
    let f2 : E (m + 1) → ℝ := fun g => (sgn (g 0) : ℝ) * f1 g
    have hf1 : MemLp f1 2 (γ (m + 1)) := hf.comp_measurePreserving (measurePreserving_isom_γ R)
    have hf_sgn_comp : (fun g : E (m + 1) => (sgn (inner ℝ g u) : ℝ) * f g) ∘ R = f2 := by
      ext g; simp [Function.comp_def, f2, f1, hinner_R g]
    have hf_sgn_memLp : MemLp (fun g : E (m + 1) => (sgn (inner ℝ g u) : ℝ) * f g) 2 (γ (m + 1)) := by
      have hsgn_meas : Measurable (fun g : E (m + 1) => (sgn (inner ℝ g u) : ℝ)) :=
        (measurable_from_top.comp
          (Measurable.ite measurableSet_Ici measurable_const measurable_const)).comp
          (continuous_id.inner continuous_const).measurable
      refine hf.of_le_mul (c := 1) (hsgn_meas.aestronglyMeasurable.mul hf.1) (ae_of_all _ fun g => ?_)
      have habs : |(sgn (inner ℝ g u) : ℝ)| = 1 := by simp only [sgn]; split_ifs <;> norm_num
      rw [one_mul, Real.norm_eq_abs, abs_mul, habs, one_mul, Real.norm_eq_abs]
    rw [← W_real_comp_isom R hf_sgn_memLp, hf_sgn_comp, ← W_real_comp_isom R hf]
    -- Now split `E (m + 1)` into `ℝ × E m`
    let splitE : E (m + 1) ≃ᵐ (ℝ × E m) :=
      { toFun := fun g => (g 0, WithLp.toLp 2 (fun j : Fin m => g j.succ))
        invFun := fun p => WithLp.toLp 2 (Fin.cons p.1 p.2.ofLp)
        left_inv := fun g => by
          ext i
          cases i using Fin.cases with
          | zero => simp
          | succ j => simp
        right_inv := fun ⟨x0, y⟩ => Prod.ext (by simp) (by ext j; simp)
        measurable_toFun := Measurable.prodMk (PiLp.continuous_apply 2 (fun _ => ℝ) 0).measurable
          (((PiLp.lipschitzWith_toLp 2 (fun _ : Fin m => ℝ)).continuous).comp
            (continuous_pi fun j => PiLp.continuous_apply 2 (fun _ => ℝ) j.succ)).measurable
        measurable_invFun := (PiLp.lipschitzWith_toLp 2 (fun _ : Fin (m + 1) => ℝ)).continuous.measurable.comp
          (measurable_pi_iff.mpr fun i => by
            cases i using Fin.cases with
            | zero => simpa using measurable_fst
            | succ j =>
              simp only [Fin.cons_succ]
              exact (PiLp.continuous_apply 2 (fun _ => ℝ) j).measurable.comp measurable_snd) }
    have hsplit_symm : ∀ p : ℝ × E m, splitE.symm p = WithLp.toLp 2 (Fin.cons p.1 p.2.ofLp) :=
      fun _ => rfl
    have hmp_split : MeasurePreserving splitE (γ (m + 1))
        ((ProbabilityTheory.gaussianReal 0 1).prod (γ m)) := by
      refine ⟨splitE.measurable, ?_⟩
      let e0 := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
      have hcomp_eq : (⇑splitE ∘ WithLp.toLp 2 : (Fin (m + 1) → ℝ) → ℝ × E m) =
          (Prod.map id (WithLp.toLp 2)) ∘ e0 := by
        ext x <;> rfl
      rw [γ, ← ProbabilityTheory.map_pi_eq_stdGaussian,
        Measure.map_map splitE.measurable
          (PiLp.lipschitzWith_toLp 2 (fun _ : Fin (m + 1) => ℝ)).continuous.measurable,
        hcomp_eq, ← Measure.map_map
          (measurable_id.prodMap
            (PiLp.lipschitzWith_toLp 2 (fun _ : Fin m => ℝ)).continuous.measurable) e0.measurable,
        (MeasureTheory.measurePreserving_piFinSuccAbove
          (fun _ : Fin (m + 1) => ProbabilityTheory.gaussianReal 0 1) 0).map_eq]
      have hprod_map : ((ProbabilityTheory.gaussianReal 0 1).prod
            (Measure.pi fun _ : Fin m => ProbabilityTheory.gaussianReal 0 1)).map
            (Prod.map id (WithLp.toLp 2)) =
          (ProbabilityTheory.gaussianReal 0 1).prod (γ m) := by
        have hm1 : MeasurePreserving (id : ℝ → ℝ)
            (ProbabilityTheory.gaussianReal 0 1) (ProbabilityTheory.gaussianReal 0 1) :=
          MeasurePreserving.id _
        have hm2 : MeasurePreserving (WithLp.toLp 2 : (Fin m → ℝ) → E m)
            (Measure.pi fun _ : Fin m => ProbabilityTheory.gaussianReal 0 1) (γ m) :=
          ⟨(PiLp.lipschitzWith_toLp 2 (fun _ : Fin m => ℝ)).continuous.measurable,
            ProbabilityTheory.map_pi_eq_stdGaussian⟩
        exact (hm1.prod hm2).map_eq
      exact hprod_map
    have hmp_symm : MeasurePreserving splitE.symm
        ((ProbabilityTheory.gaussianReal 0 1).prod (γ m)) (γ (m + 1)) := hmp_split.symm
    let consEquiv : (ℕ × (Fin m → ℕ)) ≃ (Fin (m + 1) → ℕ) :=
      { toFun := fun p => Fin.cons p.1 p.2
        invFun := fun α => (α 0, fun j => α j.succ)
        left_inv := fun ⟨k, β⟩ => Prod.ext (by simp) (funext fun j => by simp)
        right_inv := fun α => by
          ext i
          cases i using Fin.cases with
          | zero => simp
          | succ j => simp }
    have hdeg_cons : ∀ (k : ℕ) (β : Fin m → ℕ), totalDeg (Fin.cons k β) = k + totalDeg β := by
      intro k β; simp [totalDeg, Fin.sum_univ_succ]
    have hHnd_cons : ∀ (k : ℕ) (β : Fin m → ℕ) (x0 : ℝ) (y : E m),
        Hnd (Fin.cons k β) (splitE.symm (x0, y)) = h1D k x0 * Hnd β y := by
      intro k β x0 y
      rw [Hnd, Fin.prod_univ_succ, hsplit_symm]
      simp only [Fin.cons_zero, Fin.cons_succ, Hnd]
    have hf1_prod : MemLp (fun p : ℝ × E m => f1 (splitE.symm p)) 2
        ((ProbabilityTheory.gaussianReal 0 1).prod (γ m)) :=
      hf1.comp_measurePreserving hmp_symm
    have hper_beta : ∀ β : Fin m → ℕ,
        ∑' k : ℕ, ENNReal.ofReal ((1 + (totalDeg (Fin.cons k β) : ℝ)) ^ (1 / 4 : ℝ) *
            (coeff_nd f2 (Fin.cons k β)) ^ 2) ≤
          4402 * ∑' k : ℕ, ENNReal.ofReal ((1 + (totalDeg (Fin.cons k β) : ℝ)) ^ (1 / 4 : ℝ) *
            (coeff_nd f1 (Fin.cons k β)) ^ 2) := by
      intro β
      let cβ : ℝ → ℝ := fun x0 => ∫ y : E m, Hnd β y * f1 (splitE.symm (x0, y)) ∂(γ m)
      have hHnd_prod : MemLp (fun p : ℝ × E m => Hnd β p.2) 2
          ((ProbabilityTheory.gaussianReal 0 1).prod (γ m)) :=
        (memLp_Hnd β).comp_measurePreserving MeasureTheory.measurePreserving_snd
      have hprod_int : Integrable (fun p : ℝ × E m => Hnd β p.2 * f1 (splitE.symm p))
          ((ProbabilityTheory.gaussianReal 0 1).prod (γ m)) :=
        integrable_mul_of_memLp_two hHnd_prod hf1_prod
      have hcβ_int : Integrable cβ (ProbabilityTheory.gaussianReal 0 1) :=
        hprod_int.integral_prod_left
      have hf1_sq_int : Integrable (fun p : ℝ × E m => (f1 (splitE.symm p)) ^ 2)
          ((ProbabilityTheory.gaussianReal 0 1).prod (γ m)) := hf1_prod.integrable_sq
      have hcβ_memLp : MemLp cβ 2 (ProbabilityTheory.gaussianReal 0 1) := by
        rw [memLp_two_iff_integrable_sq hcβ_int.aestronglyMeasurable]
        refine (hf1_sq_int.integral_prod_left).mono' (hcβ_int.aestronglyMeasurable.pow 2) ?_
        filter_upwards [hf1_sq_int.prod_right_ae, hprod_int.prod_right_ae] with x0 hx_sq hx_p
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hnonneg : 0 ≤ ∫ y : E m, (cβ x0 * Hnd β y - f1 (splitE.symm (x0, y))) ^ 2 ∂(γ m) :=
          integral_nonneg fun _ => sq_nonneg _
        have hhi1 : Integrable (fun y : E m => (cβ x0 * Hnd β y) ^ 2) (γ m) := by
          have : (fun y : E m => (cβ x0 * Hnd β y) ^ 2) = fun y => (cβ x0) ^ 2 * (Hnd β y * Hnd β y) := by
            ext y; ring
          rw [this]
          exact (integrable_Hnd_mul_Hnd β β).const_mul _
        have hhi2 : Integrable (fun y : E m => 2 * (cβ x0 * (Hnd β y * f1 (splitE.symm (x0, y))))) (γ m) :=
          (hx_p.const_mul (cβ x0)).const_mul 2
        have hexp : (fun y : E m => (cβ x0 * Hnd β y - f1 (splitE.symm (x0, y))) ^ 2) =
            fun y => ((cβ x0 * Hnd β y) ^ 2 -
              2 * (cβ x0 * (Hnd β y * f1 (splitE.symm (x0, y))))) + (f1 (splitE.symm (x0, y))) ^ 2 := by
          ext y; ring
        have hhi12 : Integrable (fun y : E m => (cβ x0 * Hnd β y) ^ 2 -
            2 * (cβ x0 * (Hnd β y * f1 (splitE.symm (x0, y))))) (γ m) := hhi1.sub hhi2
        rw [hexp, integral_add hhi12 hx_sq, integral_sub hhi1 hhi2] at hnonneg
        have hi_sq : ∫ y : E m, (cβ x0 * Hnd β y) ^ 2 ∂(γ m) = (cβ x0) ^ 2 := by
          have : (fun y : E m => (cβ x0 * Hnd β y) ^ 2) = fun y => (cβ x0) ^ 2 * (Hnd β y * Hnd β y) := by
            ext y; ring
          rw [this, integral_const_mul, Hnd_orthonormal, if_pos rfl, mul_one]
        have hi_cross : ∫ y : E m, 2 * (cβ x0 * (Hnd β y * f1 (splitE.symm (x0, y)))) ∂(γ m) =
            2 * (cβ x0) ^ 2 := by
          rw [integral_const_mul, integral_const_mul]
          change 2 * (cβ x0 * cβ x0) = 2 * (cβ x0) ^ 2
          rw [sq]
        rw [hi_sq, hi_cross] at hnonneg
        linarith
      have hcoeff1 : ∀ k : ℕ, coeff_nd f1 (Fin.cons k β) =
          ∫ x0, h1D k x0 * cβ x0 ∂(ProbabilityTheory.gaussianReal 0 1) := by
        intro k
        rw [coeff_nd, ← hmp_symm.integral_comp' (g := fun g => Hnd (Fin.cons k β) g * f1 g)]
        have hFub : Integrable (fun p : ℝ × E m => Hnd (Fin.cons k β) (splitE.symm p) * f1 (splitE.symm p))
            ((ProbabilityTheory.gaussianReal 0 1).prod (γ m)) :=
          integrable_mul_of_memLp_two ((memLp_Hnd _).comp_measurePreserving hmp_symm) hf1_prod
        rw [integral_prod _ hFub]
        refine integral_congr_ae (ae_of_all _ fun x0 => ?_)
        dsimp only
        have heq : (fun y : E m => Hnd (Fin.cons k β) (splitE.symm (x0, y)) * f1 (splitE.symm (x0, y))) =
            fun y => h1D k x0 * (Hnd β y * f1 (splitE.symm (x0, y))) := by
          ext y; rw [hHnd_cons, mul_assoc]
        rw [heq, integral_const_mul]
      have hcoeff2 : ∀ k : ℕ, coeff_nd f2 (Fin.cons k β) =
          ∫ x0, h1D k x0 * ((sgn x0 : ℝ) * cβ x0) ∂(ProbabilityTheory.gaussianReal 0 1) := by
        intro k
        have hf2_memLp : MemLp f2 2 (γ (m + 1)) := by
          have hsgn0 : Measurable (fun g : E (m + 1) => (sgn (g 0) : ℝ)) :=
            (measurable_from_top.comp
              (Measurable.ite measurableSet_Ici measurable_const measurable_const)).comp
              (PiLp.continuous_apply 2 (fun _ => ℝ) 0).measurable
          refine hf1.of_le_mul (c := 1) (hsgn0.aestronglyMeasurable.mul hf1.1) (ae_of_all _ fun g => ?_)
          have habs : |(sgn (g 0) : ℝ)| = 1 := by simp only [sgn]; split_ifs <;> norm_num
          rw [one_mul, Real.norm_eq_abs, abs_mul, habs, one_mul, Real.norm_eq_abs]
        rw [coeff_nd, ← hmp_symm.integral_comp' (g := fun g => Hnd (Fin.cons k β) g * f2 g)]
        have hFub : Integrable (fun p : ℝ × E m => Hnd (Fin.cons k β) (splitE.symm p) * f2 (splitE.symm p))
            ((ProbabilityTheory.gaussianReal 0 1).prod (γ m)) :=
          integrable_mul_of_memLp_two ((memLp_Hnd _).comp_measurePreserving hmp_symm)
            (hf2_memLp.comp_measurePreserving hmp_symm)
        rw [integral_prod _ hFub]
        refine integral_congr_ae (ae_of_all _ fun x0 => ?_)
        dsimp only
        have hf2_split : ∀ y : E m, f2 (splitE.symm (x0, y)) = (sgn x0 : ℝ) * f1 (splitE.symm (x0, y)) := by
          intro y
          change (sgn ((splitE.symm (x0, y)) 0) : ℝ) * f1 (splitE.symm (x0, y)) = _
          rw [hsplit_symm]
          rfl
        have heq : (fun y : E m => Hnd (Fin.cons k β) (splitE.symm (x0, y)) * f2 (splitE.symm (x0, y))) =
            fun y => (h1D k x0 * (sgn x0 : ℝ)) * (Hnd β y * f1 (splitE.symm (x0, y))) := by
          ext y; rw [hHnd_cons, hf2_split]; ring
        rw [heq, integral_const_mul]
        dsimp only [cβ]; ring
      have h1d := W1D_sgn_mul (totalDeg β) hcβ_memLp
      have hdeg_real : ∀ k : ℕ, (1 + (totalDeg (Fin.cons k β) : ℝ)) =
          (k + (totalDeg β : ℝ) + 1) := by
        intro k; rw [hdeg_cons]; push_cast; ring
      simp_rw [hdeg_real, hcoeff1, hcoeff2]
      exact h1d
    let swapConsEquiv : ((Fin m → ℕ) × ℕ) ≃ (Fin (m + 1) → ℕ) :=
      (Equiv.prodComm (Fin m → ℕ) ℕ).trans consEquiv
    rw [W_real, W_real, ← swapConsEquiv.tsum_eq, ← swapConsEquiv.tsum_eq,
      ENNReal.tsum_prod', ENNReal.tsum_prod', ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun β => hper_beta β


-- Module 3: Gaussian density, spherical measure, polar factorization, cap measure, V_d dimension,
-- O(n)-invariance, and H-valued degree-<=d concentration (Lemma 3.6 ingredient).
-- Concatenated inside `namespace AuxTest1D` after `mod2_hermite_nd.lean`.

open scoped Pointwise NNReal

/-! ### Gaussian Density & Product Splitting -/

noncomputable def gaussDensity (n : ℕ) (g : E n) : ℝ :=
  (2 * Real.pi) ^ (-(n : ℝ) / 2) * Real.exp (-(‖g‖ ^ 2 / 2))

lemma gaussDensity_nonneg (n : ℕ) (g : E n) : 0 ≤ gaussDensity n g := by
  unfold gaussDensity
  positivity

lemma gaussDensity_pos (n : ℕ) (g : E n) : 0 < gaussDensity n g := by
  unfold gaussDensity
  positivity

@[fun_prop]
lemma continuous_gaussDensity (n : ℕ) : Continuous (gaussDensity n) := by
  unfold gaussDensity
  exact continuous_const.mul (Real.continuous_exp.comp
    (((continuous_norm.pow 2).div_const 2).neg))

@[fun_prop]
lemma measurable_gaussDensity (n : ℕ) : Measurable (gaussDensity n) :=
  (continuous_gaussDensity n).measurable

lemma map_withDensity_of_measurePreserving {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (e : A ≃ᵐ B) {μA : Measure A} {μB : Measure B}
    (hmp : MeasurePreserving e μA μB)
    {f : B → ℝ≥0∞} (hf : Measurable f) :
    (μA.withDensity (f ∘ e)).map e = μB.withDensity f := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs]
  calc ∫⁻ x in e ⁻¹' s, f (e x) ∂μA
      = ∫⁻ x, (e ⁻¹' s).indicator (fun x => f (e x)) x ∂μA :=
        (lintegral_indicator (e.measurable hs) _).symm
    _ = ∫⁻ x, (s.indicator f) (e x) ∂μA := by
        refine lintegral_congr fun x => ?_
        by_cases hx : e x ∈ s <;> simp [Set.indicator, hx]
    _ = ∫⁻ y, s.indicator f y ∂(μA.map e) :=
        (lintegral_map (hf.indicator hs) e.measurable).symm
    _ = ∫⁻ y, s.indicator f y ∂μB := by rw [hmp.map_eq]
    _ = ∫⁻ y in s, f y ∂μB := lintegral_indicator hs _

noncomputable def splitE_nd (m : ℕ) : E (m + 1) ≃ᵐ (ℝ × E m) where
  toFun g := (g 0, WithLp.toLp 2 (fun j : Fin m => g j.succ))
  invFun p := WithLp.toLp 2 (Fin.cons p.1 p.2.ofLp)
  left_inv g := by
    ext i
    cases i using Fin.cases with
    | zero => simp
    | succ j => simp
  right_inv := fun ⟨x0, y⟩ => Prod.ext (by simp) (by ext j; simp)
  measurable_toFun := Measurable.prodMk (PiLp.continuous_apply 2 (fun _ => ℝ) 0).measurable
    (((PiLp.lipschitzWith_toLp 2 (fun _ : Fin m => ℝ)).continuous).comp
      (continuous_pi fun j => PiLp.continuous_apply 2 (fun _ => ℝ) j.succ)).measurable
  measurable_invFun := (PiLp.lipschitzWith_toLp 2 (fun _ : Fin (m + 1) => ℝ)).continuous.measurable.comp
    (measurable_pi_iff.mpr fun i => by
      cases i using Fin.cases with
      | zero => simpa using measurable_fst
      | succ j =>
        simp only [Fin.cons_succ]
        exact (PiLp.continuous_apply 2 (fun _ => ℝ) j).measurable.comp measurable_snd)

lemma splitE_nd_symm_apply (m : ℕ) (p : ℝ × E m) :
    (splitE_nd m).symm p = WithLp.toLp 2 (Fin.cons p.1 p.2.ofLp) := rfl

lemma norm_sq_splitE_nd_symm (m : ℕ) (x0 : ℝ) (y : E m) :
    ‖(splitE_nd m).symm (x0, y)‖ ^ 2 = x0 ^ 2 + ‖y‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  rw [splitE_nd_symm_apply]
  simp only [Fin.cons_zero, Fin.cons_succ]

lemma measurePreserving_splitE_nd_γ (m : ℕ) :
    MeasurePreserving (splitE_nd m) (γ (m + 1)) ((ProbabilityTheory.gaussianReal 0 1).prod (γ m)) := by
  refine ⟨(splitE_nd m).measurable, ?_⟩
  let e0 := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  have hcomp_eq : (⇑(splitE_nd m) ∘ WithLp.toLp 2 : (Fin (m + 1) → ℝ) → ℝ × E m) =
      (Prod.map id (WithLp.toLp 2)) ∘ e0 := by
    ext x <;> rfl
  rw [γ, ← ProbabilityTheory.map_pi_eq_stdGaussian,
    Measure.map_map (splitE_nd m).measurable
      (PiLp.lipschitzWith_toLp 2 (fun _ : Fin (m + 1) => ℝ)).continuous.measurable,
    hcomp_eq, ← Measure.map_map
      (measurable_id.prodMap
        (PiLp.lipschitzWith_toLp 2 (fun _ : Fin m => ℝ)).continuous.measurable) e0.measurable,
    (MeasureTheory.measurePreserving_piFinSuccAbove
      (fun _ : Fin (m + 1) => ProbabilityTheory.gaussianReal 0 1) 0).map_eq]
  have hm1 : MeasurePreserving (id : ℝ → ℝ)
      (ProbabilityTheory.gaussianReal 0 1) (ProbabilityTheory.gaussianReal 0 1) :=
    MeasurePreserving.id _
  have hm2 : MeasurePreserving (WithLp.toLp 2 : (Fin m → ℝ) → E m)
      (Measure.pi fun _ : Fin m => ProbabilityTheory.gaussianReal 0 1) (γ m) :=
    ⟨(PiLp.lipschitzWith_toLp 2 (fun _ : Fin m => ℝ)).continuous.measurable,
      ProbabilityTheory.map_pi_eq_stdGaussian⟩
  exact (hm1.prod hm2).map_eq

lemma measurePreserving_splitE_nd_vol (m : ℕ) :
    MeasurePreserving (splitE_nd m)
      (volume : Measure (E (m + 1))) ((volume : Measure ℝ).prod (volume : Measure (E m))) := by
  refine ⟨(splitE_nd m).measurable, ?_⟩
  let e0 := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  have hcomp_eq : (⇑(splitE_nd m) ∘ WithLp.toLp 2 : (Fin (m + 1) → ℝ) → ℝ × E m) =
      (Prod.map id (WithLp.toLp 2)) ∘ e0 := by
    ext x <;> rfl
  have hvol_map : ((volume : Measure (Fin (m + 1) → ℝ)).map (WithLp.toLp 2)) =
      (volume : Measure (E (m + 1))) :=
    (PiLp.volume_preserving_toLp (Fin (m + 1))).map_eq
  rw [← hvol_map,
    Measure.map_map (splitE_nd m).measurable
      (PiLp.lipschitzWith_toLp 2 (fun _ : Fin (m + 1) => ℝ)).continuous.measurable,
    hcomp_eq, ← Measure.map_map
      (measurable_id.prodMap
        (PiLp.lipschitzWith_toLp 2 (fun _ : Fin m => ℝ)).continuous.measurable) e0.measurable]
  have hpi : (volume : Measure (Fin (m + 1) → ℝ)) = Measure.pi fun _ : Fin (m + 1) => volume := rfl
  have hpi_m : (volume : Measure (Fin m → ℝ)) = Measure.pi fun _ : Fin m => volume := rfl
  rw [hpi, (MeasureTheory.measurePreserving_piFinSuccAbove
    (fun _ : Fin (m + 1) => (volume : Measure ℝ)) 0).map_eq, ← hpi_m]
  have hm1 : MeasurePreserving (id : ℝ → ℝ) volume volume := MeasurePreserving.id _
  have hm2 : MeasurePreserving (WithLp.toLp 2 : (Fin m → ℝ) → E m) volume volume :=
    PiLp.volume_preserving_toLp (Fin m)
  exact (hm1.prod hm2).map_eq

lemma gaussianReal_zero_one_eq_withDensity :
    ProbabilityTheory.gaussianReal 0 1 =
      (volume : Measure ℝ).withDensity (fun x =>
        ENNReal.ofReal ((2 * Real.pi) ^ (-(1 : ℝ) / 2) * Real.exp (-(x ^ 2 / 2)))) := by
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero 0 one_ne_zero]
  congr 1
  ext x
  rw [ProbabilityTheory.gaussianPDF_def, ProbabilityTheory.gaussianPDFReal_def]
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hcoef : (Real.sqrt (2 * Real.pi))⁻¹ = (2 * Real.pi) ^ (-(1 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg h2pi.le, neg_div]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [hcoef]
  congr 3
  ring

lemma γ_eq_volume_withDensity (n : ℕ) :
    γ n = (volume : Measure (E n)).withDensity (fun g => ENNReal.ofReal (gaussDensity n g)) := by
  induction n with
  | zero =>
    have hvol_univ : (volume : Measure (E 0)) Set.univ = 1 := by
      have hmp := (PiLp.volume_preserving_toLp (Fin 0)).measure_preimage
        (MeasurableSet.univ (α := E 0)).nullMeasurableSet
      rw [Set.preimage_univ,
        show (volume : Measure (Fin 0 → ℝ)) = Measure.pi (fun _ => volume) from rfl,
        Measure.pi_empty_univ] at hmp
      exact hmp.symm
    have hdens0 : ∀ g : E 0, ENNReal.ofReal (gaussDensity 0 g) = 1 := by
      intro g
      rw [Subsingleton.elim g 0]
      simp [gaussDensity]
    ext s _
    by_cases hs : (0 : E 0) ∈ s
    · have hsu : s = Set.univ := Set.eq_univ_of_forall fun x => by
        rwa [Subsingleton.elim x (0 : E 0)]
      rw [hsu, measure_univ, withDensity_apply _ MeasurableSet.univ]
      simp_rw [hdens0]
      simp [hvol_univ]
    · have hse : s = ∅ := Set.eq_empty_of_forall_notMem fun x hx => by
        rw [Subsingleton.elim x (0 : E 0)] at hx; exact hs hx
      rw [hse, measure_empty, measure_empty]
  | succ m ih =>
    have hsplit_γ := measurePreserving_splitE_nd_γ m
    have hsplit_vol := measurePreserving_splitE_nd_vol m
    have hsymm_γ : ((ProbabilityTheory.gaussianReal 0 1).prod (γ m)).map (splitE_nd m).symm =
        γ (m + 1) :=
      hsplit_γ.symm.map_eq
    rw [← hsymm_γ, gaussianReal_zero_one_eq_withDensity, ih, MeasureTheory.prod_withDensity]
    · have hdens_eq : (fun p : ℝ × E m =>
          ENNReal.ofReal ((2 * Real.pi) ^ (-(1 : ℝ) / 2) * Real.exp (-(p.1 ^ 2 / 2))) *
            ENNReal.ofReal (gaussDensity m p.2)) =
          (fun g => ENNReal.ofReal (gaussDensity (m + 1) g)) ∘ (splitE_nd m).symm := by
        ext ⟨x0, y⟩
        rw [Function.comp_def, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        unfold gaussDensity
        rw [norm_sq_splitE_nd_symm]
        have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
        have hpow : (2 * Real.pi) ^ (-(1 : ℝ) / 2) * (2 * Real.pi) ^ (-(m : ℝ) / 2) =
            (2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) := by
          rw [← Real.rpow_add h2pi]
          congr 1
          push_cast
          ring
        have hexp : Real.exp (-(x0 ^ 2 / 2)) * Real.exp (-(‖y‖ ^ 2 / 2)) =
            Real.exp (-((x0 ^ 2 + ‖y‖ ^ 2) / 2)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc (2 * Real.pi) ^ (-(1 : ℝ) / 2) * Real.exp (-(x0 ^ 2 / 2)) *
              ((2 * Real.pi) ^ (-(m : ℝ) / 2) * Real.exp (-(‖y‖ ^ 2 / 2)))
            = ((2 * Real.pi) ^ (-(1 : ℝ) / 2) * (2 * Real.pi) ^ (-(m : ℝ) / 2)) *
                (Real.exp (-(x0 ^ 2 / 2)) * Real.exp (-(‖y‖ ^ 2 / 2))) := by ring
          _ = (2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) *
                Real.exp (-((x0 ^ 2 + ‖y‖ ^ 2) / 2)) := by rw [hpow, hexp]
      rw [hdens_eq]
      exact map_withDensity_of_measurePreserving (splitE_nd m).symm hsplit_vol.symm
        (measurable_gaussDensity (m + 1)).ennreal_ofReal
    · exact ((continuous_const.mul (Real.continuous_exp.comp
        (((continuous_pow 2).div_const 2).neg))).measurable).ennreal_ofReal
    · exact (measurable_gaussDensity m).ennreal_ofReal

/-! ### Normalized Spherical Measure `μS`, `O(n)`-Invariance, & Polar Factorization -/

lemma nontrivial_E {n : ℕ} (hn : 1 ≤ n) : Nontrivial (E n) := by
  refine ⟨⟨EuclideanSpace.single ⟨0, hn⟩ 1, 0, ?_⟩⟩
  intro h
  have := congrArg (fun v : E n => v ⟨0, hn⟩) h
  simp at this

lemma toSphere_real_univ_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < (volume : Measure (E n)).toSphere.real Set.univ := by
  have : Nontrivial (E n) := nontrivial_E hn
  rw [Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin]
  have hball_pos : 0 < (volume : Measure (E n)).real (Metric.ball 0 1) := by
    rw [Measure.real, ENNReal.toReal_pos_iff]
    exact ⟨Metric.isOpen_ball.measure_pos _ ⟨0, Metric.mem_ball_self (x := (0 : E n)) one_pos⟩,
      MeasureTheory.measure_ball_lt_top⟩
  have hn_pos : (0 : ℝ) < n := by positivity
  exact mul_pos hn_pos hball_pos

noncomputable def μS (n : ℕ) : Measure (Metric.sphere (0 : E n) 1) :=
  (ENNReal.ofReal ((volume : Measure (E n)).toSphere.real Set.univ))⁻¹ •
    (volume : Measure (E n)).toSphere

lemma isProbabilityMeasure_μS {n : ℕ} (hn : 1 ≤ n) : IsProbabilityMeasure (μS n) := by
  have : Nontrivial (E n) := nontrivial_E hn
  refine ⟨?_⟩
  have hc_pos : 0 < (volume : Measure (E n)).toSphere.real Set.univ := toSphere_real_univ_pos hn
  have hlt : (volume : Measure (E n)).toSphere Set.univ < ⊤ := MeasureTheory.measure_lt_top _ _
  have hofReal : ENNReal.ofReal ((volume : Measure (E n)).toSphere.real Set.univ) =
      (volume : Measure (E n)).toSphere Set.univ :=
    ENNReal.ofReal_toReal hlt.ne
  rw [μS, Measure.smul_apply, smul_eq_mul, hofReal,
    ENNReal.inv_mul_cancel ((ENNReal.ofReal_pos.mpr hc_pos).trans_eq hofReal).ne' hlt.ne]

lemma isOpenPosMeasure_μS {n : ℕ} (hn : 1 ≤ n) : (μS n).IsOpenPosMeasure := by
  have : Nontrivial (E n) := nontrivial_E hn
  refine ⟨fun U hUo hUne => ?_⟩
  rw [μS, Measure.smul_apply, smul_eq_mul]
  refine mul_ne_zero ?_ (hUo.measure_pos (volume : Measure (E n)).toSphere hUne).ne'
  rw [ne_eq, ENNReal.inv_eq_zero]
  exact ENNReal.ofReal_ne_top

noncomputable def sphereHomeo {n : ℕ} (R : E n ≃ₗᵢ[ℝ] E n) :
    Metric.sphere (0 : E n) 1 ≃ₜ Metric.sphere (0 : E n) 1 where
  toFun ω := ⟨R ω.1, mem_sphere_zero_iff_norm.mpr (by rw [R.norm_map]; exact mem_sphere_zero_iff_norm.mp ω.2)⟩
  invFun ω := ⟨R.symm ω.1, mem_sphere_zero_iff_norm.mpr (by rw [R.symm.norm_map]; exact mem_sphere_zero_iff_norm.mp ω.2)⟩
  left_inv ω := Subtype.ext (R.symm_apply_apply ω.1)
  right_inv ω := Subtype.ext (R.apply_symm_apply ω.1)
  continuous_toFun := Continuous.subtype_mk (R.continuous.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk (R.symm.continuous.comp continuous_subtype_val) _

lemma sector_eq_image_preimage_unitSphereProd {n : ℕ} (s : Set (Metric.sphere (0 : E n) 1)) :
    Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s) =
      Subtype.val '' ((homeomorphUnitSphereProd (E n)) ⁻¹' (s ×ˢ Set.Iio ⟨1, Set.mem_Ioi.mpr one_pos⟩)) := by
  ext x
  constructor
  · rintro ⟨r, hr, v, ⟨w, hw, rfl⟩, rfl⟩
    have hw_norm : ‖w.1‖ = 1 := mem_sphere_zero_iff_norm.mp w.2
    have hw_ne : w.1 ≠ 0 := fun h0 => by rw [h0, norm_zero] at hw_norm; norm_num at hw_norm
    have hx_ne : r • w.1 ≠ 0 := smul_ne_zero hr.1.ne' hw_ne
    have hnorm_x : ‖r • w.1‖ = r := by
      rw [norm_smul, Real.norm_of_nonneg hr.1.le, hw_norm, mul_one]
    have hunit : ‖r • w.1‖⁻¹ • (r • w.1) = w.1 := by
      rw [hnorm_x, smul_smul, inv_mul_cancel₀ hr.1.ne', one_smul]
    refine ⟨⟨r • w.1, hx_ne⟩, ?_, rfl⟩
    rw [Set.mem_preimage, Set.mem_prod, Set.mem_Iio]
    refine ⟨?_, ?_⟩
    · have heq : (homeomorphUnitSphereProd (E n) ⟨r • w.1, hx_ne⟩).1 = w := by
        ext1
        rw [homeomorphUnitSphereProd_apply_fst_coe]
        exact hunit
      rwa [heq]
    · change ((homeomorphUnitSphereProd (E n) ⟨r • w.1, hx_ne⟩).2 : ℝ) < 1
      rw [homeomorphUnitSphereProd_apply_snd_coe, hnorm_x]
      exact hr.2
  · rintro ⟨⟨x0, hx0⟩, hxmem, rfl⟩
    rw [Set.mem_preimage, Set.mem_prod, Set.mem_Iio] at hxmem
    have hnorm_pos : 0 < ‖x0‖ := norm_pos_iff.mpr hx0
    have hlt : ‖x0‖ < 1 := by
      have h2 : ((homeomorphUnitSphereProd (E n) ⟨x0, hx0⟩).2 : ℝ) < 1 := hxmem.2
      simpa [homeomorphUnitSphereProd_apply_snd_coe] using h2
    let w0 : Metric.sphere (0 : E n) 1 :=
      ⟨‖x0‖⁻¹ • x0, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hx0)⟩
    have hw0_mem : w0 ∈ s := by
      have heq : w0 = (homeomorphUnitSphereProd (E n) ⟨x0, hx0⟩).1 := by
        ext1
        exact (homeomorphUnitSphereProd_apply_fst_coe (E n) ⟨x0, hx0⟩).symm
      rw [heq]
      exact hxmem.1
    exact ⟨‖x0‖, ⟨hnorm_pos, hlt⟩, w0.1, ⟨w0, hw0_mem, rfl⟩, smul_inv_smul₀ hnorm_pos.ne' x0⟩

lemma measurePreserving_sphereHomeo {n : ℕ} (hn : 1 ≤ n) (R : E n ≃ₗᵢ[ℝ] E n) :
    MeasurePreserving (sphereHomeo R) (μS n) (μS n) := by
  have : Nontrivial (E n) := nontrivial_E hn
  refine ⟨(sphereHomeo R).continuous.measurable, ?_⟩
  have hto : ((volume : Measure (E n)).toSphere).map (sphereHomeo R) =
      (volume : Measure (E n)).toSphere := by
    ext s hs
    rw [Measure.map_apply (sphereHomeo R).continuous.measurable hs,
      Measure.toSphere_apply' _ ((sphereHomeo R).continuous.measurable hs),
      Measure.toSphere_apply' _ hs]
    congr 1
    have himg : Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereHomeo R ⁻¹' s)) =
        R ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
      ext x
      rw [Set.mem_preimage]
      constructor
      · rintro ⟨r, hr, v, ⟨w, hw, rfl⟩, rfl⟩
        refine ⟨r, hr, R w.1,
          ⟨⟨R w.1, mem_sphere_zero_iff_norm.mpr (by rw [R.norm_map]; exact mem_sphere_zero_iff_norm.mp w.2)⟩,
            hw, rfl⟩, ?_⟩
        exact (map_smul R r w.1).symm
      · rintro ⟨r, hr, v, ⟨w, hw, rfl⟩, hRxv⟩
        let w' : Metric.sphere (0 : E n) 1 :=
          ⟨R.symm w.1, mem_sphere_zero_iff_norm.mpr (by rw [R.symm.norm_map]; exact mem_sphere_zero_iff_norm.mp w.2)⟩
        have hw'_mem : w' ∈ sphereHomeo R ⁻¹' s := by
          rw [Set.mem_preimage]
          have heq : sphereHomeo R w' = w := by ext1; simp [sphereHomeo, w']
          rwa [heq]
        refine ⟨r, hr, w'.1, ⟨w', hw'_mem, rfl⟩, ?_⟩
        change r • w'.1 = x
        dsimp [w']
        change r • w.1 = R x at hRxv
        rw [← map_smul R.symm r w.1, hRxv, R.symm_apply_apply]
    have hmeas_sec : MeasurableSet (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
      rw [sector_eq_image_preimage_unitSphereProd]
      exact ((MeasurableEmbedding.subtype_coe (measurableSet_singleton _).compl).measurableSet_image).mpr
        ((homeomorphUnitSphereProd (E n)).continuous.measurable (hs.prod measurableSet_Iio))
    rw [himg]
    exact (R.measurePreserving (E := E n) (F := E n)).measure_preimage hmeas_sec.nullMeasurableSet
  rw [μS, Measure.map_smul, hto]

noncomputable def radDensity (n : ℕ) (r : ℝ) : ℝ :=
  (2 * Real.pi) ^ (-(n : ℝ) / 2) * Real.exp (-(r ^ 2 / 2))

noncomputable def radialWeight (n : ℕ) (r : ℝ) : ℝ :=
  (volume : Measure (E n)).toSphere.real Set.univ * radDensity n r * r ^ (n - 1)

lemma radialWeight_nonneg {n : ℕ} {r : ℝ} (hr : 0 ≤ r) : 0 ≤ radialWeight n r := by
  unfold radialWeight radDensity
  positivity

lemma integral_gamma_polar {n : ℕ} (hn : 2 ≤ n) {F : E n → ℝ} (hF : Integrable F (γ n)) :
    (∫ g : E n, F g ∂(γ n) =
      ∫ r in Set.Ioi (0 : ℝ), radialWeight n r *
        ∫ ω : Metric.sphere (0 : E n) 1, F (r • ω.1) ∂(μS n)) ∧
    Integrable (fun r : ℝ => radialWeight n r *
        ∫ ω : Metric.sphere (0 : E n) 1, F (r • ω.1) ∂(μS n))
      ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  have : Nontrivial (E n) := nontrivial_E hn1
  have hγ_nn : γ n = (volume : Measure (E n)).withDensity
      (fun g => ((gaussDensity n g).toNNReal : ℝ≥0∞)) := by
    rw [γ_eq_volume_withDensity]
    rfl
  have hG_int : Integrable (fun g : E n => gaussDensity n g * F g) volume := by
    rw [hγ_nn, integrable_withDensity_iff_integrable_smul' (by fun_prop)
      (ae_of_all _ fun _ => ENNReal.coe_lt_top)] at hF
    refine hF.congr (ae_of_all _ fun g => ?_)
    dsimp only
    rw [ENNReal.coe_toReal, Real.coe_toNNReal _ (gaussDensity_nonneg n g), smul_eq_mul]
  have hG_int_eq : ∫ g : E n, F g ∂(γ n) = ∫ g : E n, gaussDensity n g * F g ∂volume := by
    rw [hγ_nn, integral_withDensity_eq_integral_smul (by fun_prop)]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    dsimp only
    rw [NNReal.smul_def, Real.coe_toNNReal _ (gaussDensity_nonneg n g), smul_eq_mul]
  have hvol_compl_meas : MeasurableSet (({0}ᶜ : Set (E n))) :=
    (measurableSet_singleton _).compl
  have hG_comap_int : Integrable (fun x : ({0}ᶜ : Set (E n)) => gaussDensity n x.1 * F x.1)
      ((volume : Measure (E n)).comap Subtype.val) := by
    change Integrable ((fun g : E n => gaussDensity n g * F g) ∘ Subtype.val)
      ((volume : Measure (E n)).comap Subtype.val)
    rw [← integrableOn_iff_comap_subtypeVal hvol_compl_meas]
    exact hG_int.integrableOn
  have hG_comap_eq : ∫ g : E n, gaussDensity n g * F g ∂volume =
      ∫ x : ({0}ᶜ : Set (E n)), gaussDensity n x.1 * F x.1 ∂((volume : Measure (E n)).comap Subtype.val) := by
    rw [integral_subtype_comap hvol_compl_meas (fun g : E n => gaussDensity n g * F g),
      restrict_compl_singleton]
  let ePM : ({0}ᶜ : Set (E n)) ≃ᵐ (Metric.sphere (0 : E n) 1 × Set.Ioi (0 : ℝ)) :=
    (homeomorphUnitSphereProd (E n)).toMeasurableEquiv
  have hmp_homeo := (volume : Measure (E n)).measurePreserving_homeomorphUnitSphereProd
  have hmp_pol : MeasurePreserving ePM ((volume : Measure (E n)).comap Subtype.val)
      ((volume : Measure (E n)).toSphere.prod (Measure.volumeIoiPow (n - 1))) := by
    refine ⟨ePM.measurable, ?_⟩
    simpa [ePM, finrank_euclideanSpace_fin] using hmp_homeo.map_eq
  let H : Metric.sphere (0 : E n) 1 × Set.Ioi (0 : ℝ) → ℝ :=
    fun p => radDensity n p.2.1 * F (p.2.1 • p.1.1)
  have hH_comp : (fun p : Metric.sphere (0 : E n) 1 × Set.Ioi (0 : ℝ) =>
        gaussDensity n (ePM.symm p).1 * F (ePM.symm p).1) = H := by
    ext ⟨ω, r⟩
    have hr_pos : 0 < r.1 := r.2
    have hω_norm : ‖ω.1‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
    have hsymm : (ePM.symm (ω, r)).1 = r.1 • ω.1 := rfl
    rw [hsymm]
    dsimp only [H, gaussDensity, radDensity]
    rw [norm_smul, Real.norm_of_nonneg hr_pos.le, hω_norm, mul_one]
  have hH_int : Integrable H ((volume : Measure (E n)).toSphere.prod (Measure.volumeIoiPow (n - 1))) := by
    rw [← hH_comp]
    exact (hmp_pol.symm.integrable_comp_emb ePM.symm.measurableEmbedding).mpr hG_comap_int
  have hH_eq : ∫ x : ({0}ᶜ : Set (E n)), gaussDensity n x.1 * F x.1 ∂((volume : Measure (E n)).comap Subtype.val) =
      ∫ p : Metric.sphere (0 : E n) 1 × Set.Ioi (0 : ℝ), H p
        ∂((volume : Measure (E n)).toSphere.prod (Measure.volumeIoiPow (n - 1))) := by
    calc ∫ x : ({0}ᶜ : Set (E n)), gaussDensity n x.1 * F x.1 ∂((volume : Measure (E n)).comap Subtype.val)
        = ∫ x : ({0}ᶜ : Set (E n)), H (ePM x) ∂((volume : Measure (E n)).comap Subtype.val) := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          have hx : (ePM.symm (ePM x)).1 = x.1 := by rw [ePM.symm_apply_apply]
          rw [← hH_comp]
          dsimp only
          rw [hx]
      _ = ∫ p, H p ∂((volume : Measure (E n)).toSphere.prod (Measure.volumeIoiPow (n - 1))) :=
          hmp_pol.integral_comp ePM.measurableEmbedding H
  have : SFinite (volume : Measure (E n)).toSphere := inferInstance
  have : SFinite (Measure.volumeIoiPow (n - 1)) := inferInstance
  have hc_pos : 0 < (volume : Measure (E n)).toSphere.real Set.univ := toSphere_real_univ_pos hn1
  have hc_top : (volume : Measure (E n)).toSphere Set.univ < ⊤ := MeasureTheory.measure_lt_top _ _
  have htoSphere_eq : (volume : Measure (E n)).toSphere =
      ENNReal.ofReal ((volume : Measure (E n)).toSphere.real Set.univ) • μS n := by
    rw [μS, smul_smul, ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hc_pos).ne'
      ENNReal.ofReal_ne_top, one_smul]
  have hinner_eq : ∀ r : Set.Ioi (0 : ℝ),
      (∫ ω : Metric.sphere (0 : E n) 1, H (ω, r) ∂(volume : Measure (E n)).toSphere) =
        radDensity n r.1 *
          ((volume : Measure (E n)).toSphere.real Set.univ *
            ∫ ω : Metric.sphere (0 : E n) 1, F (r.1 • ω.1) ∂(μS n)) := by
    intro r
    simp only [H, integral_const_mul]
    conv_lhs => rw [htoSphere_eq, integral_smul_measure, ENNReal.toReal_ofReal hc_pos.le, smul_eq_mul]
  have hr_int_IoiPow : Integrable (fun r : Set.Ioi (0 : ℝ) =>
        radDensity n r.1 * ((volume : Measure (E n)).toSphere.real Set.univ *
          ∫ ω : Metric.sphere (0 : E n) 1, F (r.1 • ω.1) ∂(μS n)))
      (Measure.volumeIoiPow (n - 1)) :=
    (hH_int.integral_prod_right).congr (ae_of_all _ hinner_eq)
  have hr_int_vol : Integrable (fun r : ℝ => radialWeight n r *
        ∫ ω : Metric.sphere (0 : E n) 1, F (r • ω.1) ∂(μS n))
      ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
    rw [Measure.volumeIoiPow] at hr_int_IoiPow
    have hr_dens_eq : (Measure.withDensity ((volume : Measure ℝ).comap Subtype.val)
          fun r : Set.Ioi (0 : ℝ) => ENNReal.ofReal (r.1 ^ (n - 1))) =
        (Measure.withDensity ((volume : Measure ℝ).comap Subtype.val)
          fun r : Set.Ioi (0 : ℝ) => ((r.1 ^ (n - 1)).toNNReal : ℝ≥0∞)) := rfl
    rw [hr_dens_eq, integrable_withDensity_iff_integrable_smul' (by fun_prop)
      (ae_of_all _ fun _ => ENNReal.coe_lt_top)] at hr_int_IoiPow
    have hcomap : Integrable (fun r : Set.Ioi (0 : ℝ) => radialWeight n r.1 *
          ∫ ω : Metric.sphere (0 : E n) 1, F (r.1 • ω.1) ∂(μS n))
        ((volume : Measure ℝ).comap Subtype.val) := by
      refine hr_int_IoiPow.congr (ae_of_all _ fun r => ?_)
      dsimp only
      rw [ENNReal.coe_toReal, Real.coe_toNNReal _ (pow_nonneg r.2.le _)]
      unfold radialWeight
      ring
    exact (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mpr hcomap
  refine ⟨?_, hr_int_vol⟩
  have hint_prod : ∫ p : Metric.sphere (0 : E n) 1 × Set.Ioi (0 : ℝ), H p
        ∂((volume : Measure (E n)).toSphere.prod (Measure.volumeIoiPow (n - 1))) =
      ∫ r : Set.Ioi (0 : ℝ),
        ((volume : Measure (E n)).toSphere.real Set.univ * radDensity n r.1 *
          ∫ ω : Metric.sphere (0 : E n) 1, F (r.1 • ω.1) ∂(μS n))
        ∂(Measure.volumeIoiPow (n - 1)) := by
    rw [integral_prod_symm _ hH_int]
    refine integral_congr_ae (ae_of_all _ fun r => ?_)
    dsimp only
    rw [hinner_eq r]
    ring
  rw [hG_int_eq, hG_comap_eq, hH_eq, hint_prod]
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul ((measurable_subtype_coe.pow_const _).real_toNNReal)]
  have hrewrite : ∫ r : Set.Ioi (0 : ℝ),
        ((r.1 ^ (n - 1)).toNNReal •
          ((volume : Measure (E n)).toSphere.real Set.univ * radDensity n r.1 *
            ∫ ω : Metric.sphere (0 : E n) 1, F (r.1 • ω.1) ∂(μS n)))
        ∂((volume : Measure ℝ).comap Subtype.val) =
      ∫ r : Set.Ioi (0 : ℝ),
        (radialWeight n r.1 * ∫ ω : Metric.sphere (0 : E n) 1, F (r.1 • ω.1) ∂(μS n))
        ∂((volume : Measure ℝ).comap Subtype.val) := by
    refine integral_congr_ae (ae_of_all _ fun r => ?_)
    dsimp only
    rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg r.2.le _), smul_eq_mul]
    unfold radialWeight
    ring
  rw [hrewrite, ← integral_subtype_comap measurableSet_Ioi
    (fun r : ℝ => radialWeight n r * ∫ ω : Metric.sphere (0 : E n) 1, F (r • ω.1) ∂(μS n))]

def cone {n : ℕ} (A : Set (Metric.sphere (0 : E n) 1)) : Set (E n) :=
  {g : E n | g ≠ 0 ∧ ‖g‖⁻¹ • g ∈ Subtype.val '' A}

lemma measurableSet_cone {n : ℕ} {A : Set (Metric.sphere (0 : E n) 1)} (hA : MeasurableSet A) :
    MeasurableSet (cone A) := by
  have himg : MeasurableSet (Subtype.val '' A) :=
    (MeasurableEmbedding.subtype_coe (Metric.isClosed_sphere.measurableSet)).measurableSet_image.mpr hA
  have hnorm_meas : Measurable (fun g : E n => ‖g‖⁻¹ • g) :=
    (continuous_norm.measurable.inv).smul measurable_id
  exact (measurableSet_singleton (0 : E n)).compl.inter (hnorm_meas himg)

lemma cone_indicator_radial {n : ℕ} (A : Set (Metric.sphere (0 : E n) 1))
    (F : E n → ℝ) {r : ℝ} (hr : 0 < r) (ω : Metric.sphere (0 : E n) 1) :
    (cone A).indicator F (r • ω.1) = A.indicator (fun ω' : Metric.sphere (0 : E n) 1 => F (r • ω'.1)) ω := by
  have hω_norm : ‖ω.1‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
  have hω_ne : ω.1 ≠ 0 := by intro h; rw [h, norm_zero] at hω_norm; norm_num at hω_norm
  have hrω_ne : r • ω.1 ≠ 0 := smul_ne_zero hr.ne' hω_ne
  have hrω_norm : ‖r • ω.1‖ = r := by
    rw [norm_smul, Real.norm_of_nonneg hr.le, hω_norm, mul_one]
  have hunit : ‖r • ω.1‖⁻¹ • (r • ω.1) = ω.1 := by
    rw [hrω_norm, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  have hmem : (r • ω.1) ∈ cone A ↔ ω ∈ A := by
    simp only [cone, Set.mem_ofPred_eq, hrω_ne, ne_eq, not_false_eq_true, true_and, hunit,
      Set.mem_image, Subtype.exists]
    exact ⟨fun ⟨w, _, hwA, hw_eq⟩ => by convert hwA using 1; exact Subtype.ext hw_eq.symm,
      fun h => ⟨ω.1, ω.2, h, rfl⟩⟩
  by_cases h : ω ∈ A
  · simp [Set.indicator, h, hmem.mpr h]
  · simp [Set.indicator, h, mt hmem.mp h]

/-! ### Elementary Spherical Cap Measure Bound -/

lemma μS_cap_le {n : ℕ} (hn : 2 ≤ n) (u₀ : Metric.sphere (0 : E n) 1)
    {θ : ℝ} (hθ_pos : 0 < θ) (hθ_le : θ ≤ Real.pi / 2) :
    (μS n).real {ω : Metric.sphere (0 : E n) 1 | Real.cos θ ≤ inner ℝ ω.1 u₀.1} ≤
      (2 * θ) ^ (n - 1) := by
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨m, rfl⟩
  have hm_ge : 1 ≤ m := by omega
  have hu₀_norm : ‖u₀.1‖ = 1 := mem_sphere_zero_iff_norm.mp u₀.2
  obtain ⟨b, hb0⟩ := exists_orthonormalBasis_zero u₀.1 hu₀_norm
  let R : E (m + 1) ≃ₗᵢ[ℝ] E (m + 1) :=
    (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).equiv b (Equiv.refl _)
  have hR0 : R (EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0) = u₀.1 := by
    dsimp [R]; rw [OrthonormalBasis.equiv_apply_basis, Equiv.refl_apply, hb0]
  let Cap : Set (Metric.sphere (0 : E (m + 1)) 1) :=
    {ω | Real.cos θ ≤ inner ℝ ω.1 u₀.1}
  let Cap0 : Set (Metric.sphere (0 : E (m + 1)) 1) :=
    {ω | Real.cos θ ≤ ω.1 0}
  have hpre : sphereHomeo R ⁻¹' Cap = Cap0 := by
    ext ω
    simp only [Set.mem_preimage, Cap, Cap0, Set.mem_ofPred_eq]
    have hin : inner ℝ (R ω.1) u₀.1 = ω.1 0 := by
      rw [← hR0, R.inner_map_eq_flip, R.symm_apply_apply,
        EuclideanSpace.inner_basisFun_real (Fin (m + 1))]
    change Real.cos θ ≤ inner ℝ (R ω.1) u₀.1 ↔ Real.cos θ ≤ ω.1 0
    rw [hin]
  have hmeas_cap : MeasurableSet Cap := by
    change MeasurableSet {ω : Metric.sphere (0 : E (m + 1)) 1 | Real.cos θ ≤ inner ℝ ω.1 u₀.1}
    exact measurableSet_le measurable_const ((continuous_subtype_val.inner continuous_const).measurable)
  have hmp_s := measurePreserving_sphereHomeo (by omega : 1 ≤ m + 1) R
  have hcap_eq : (μS (m + 1)).real Cap = (μS (m + 1)).real Cap0 := by
    rw [Measure.real, Measure.real, ← hmp_s.measure_preimage hmeas_cap.nullMeasurableSet, hpre]
  rw [hcap_eq]
  have hmeas_cap0 : MeasurableSet Cap0 := by
    change MeasurableSet {ω : Metric.sphere (0 : E (m + 1)) 1 | Real.cos θ ≤ ω.1 0}
    exact measurableSet_le measurable_const
      ((PiLp.continuous_apply 2 (fun _ => ℝ) 0).comp continuous_subtype_val).measurable
  have hc_pos : 0 < (volume : Measure (E (m + 1))).toSphere.real Set.univ :=
    toSphere_real_univ_pos (by omega)
  have hratio_def : (μS (m + 1)).real Cap0 =
      ((volume : Measure (E (m + 1))).toSphere.real Cap0) /
        ((volume : Measure (E (m + 1))).toSphere.real Set.univ) := by
    rw [μS, Measure.real, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_inv, ENNReal.toReal_ofReal hc_pos.le, inv_mul_eq_div]
    rfl
  rw [hratio_def]
  have hnum_vol : (volume : Measure (E (m + 1))).toSphere.real Cap0 =
      (m + 1 : ℝ) * (volume : Measure (E (m + 1))).real (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' Cap0)) := by
    rw [Measure.real, Measure.toSphere_apply' _ hmeas_cap0, finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_natCast, Nat.cast_add, Nat.cast_one]
    rfl
  have hden_vol : (volume : Measure (E (m + 1))).toSphere.real Set.univ =
      (m + 1 : ℝ) * (volume : Measure (E (m + 1))).real (Metric.ball (0 : E (m + 1)) 1) := by
    have : Nontrivial (E (m + 1)) := nontrivial_E (by omega)
    rw [Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin, Nat.cast_add, Nat.cast_one]
  rw [hnum_vol, hden_vol, mul_div_mul_left _ _ (by positivity : (m + 1 : ℝ) ≠ 0)]
  -- Compare via `splitE_nd m : E (m + 1) ≃ᵐ (ℝ × E m)`
  have hmp_vol := measurePreserving_splitE_nd_vol m
  let sec := Set.Ioo (0 : ℝ) 1 • (Subtype.val '' Cap0)
  let box_top : Set (ℝ × E m) := Set.Ico 0 1 ×ˢ Metric.ball (0 : E m) ((5 / 4 : ℝ) * θ)
  let box_bot : Set (ℝ × E m) := Set.Ioo (-1 / 2 : ℝ) (1 / 2) ×ˢ Metric.ball (0 : E m) (Real.sqrt 3 / 2)
  have hsec_sub : sec ⊆ (splitE_nd m) ⁻¹' box_top := by
    intro y hy
    rcases hy with ⟨r, hr, v, ⟨ω, hω_cap, rfl⟩, rfl⟩
    change (r • ω.1) 0 ∈ Set.Ico (0 : ℝ) 1 ∧
      WithLp.toLp 2 (fun j : Fin m => (r • ω.1) j.succ) ∈ Metric.ball (0 : E m) ((5 / 4 : ℝ) * θ)
    have hω_norm : ‖ω.1‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
    have hcos_nn : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hθ_le⟩
    have hω0_ge : Real.cos θ ≤ ω.1 0 := hω_cap
    have hω0_le : ω.1 0 ≤ 1 := by
      have h1 : |ω.1 0| ≤ ‖ω.1‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le ω.1 0
      rw [hω_norm] at h1
      exact (abs_le.mp h1).2
    constructor
    · refine ⟨mul_nonneg hr.1.le (hcos_nn.trans hω0_ge), ?_⟩
      change r * ω.1 0 < 1
      nlinarith [hr.1, hr.2]
    · rw [Metric.mem_ball, dist_zero_right]
      have hnorm_sq : ‖WithLp.toLp 2 (fun j : Fin m => (r • ω.1) j.succ)‖ ^ 2 ≤ θ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        have hsum_ω : (ω.1 0) ^ 2 + ∑ j : Fin m, (ω.1 j.succ) ^ 2 = 1 := by
          have h1 := EuclideanSpace.real_norm_sq_eq ω.1
          rw [hω_norm, one_pow, Fin.sum_univ_succ] at h1
          exact h1.symm
        have hsum_perp : ∑ j : Fin m, ((r • ω.1) j.succ) ^ 2 =
            r ^ 2 * ∑ j : Fin m, (ω.1 j.succ) ^ 2 := by
          simp_rw [PiLp.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
        change ∑ j : Fin m, ((r • ω.1) j.succ) ^ 2 ≤ θ ^ 2
        rw [hsum_perp]
        have htail_le : ∑ j : Fin m, (ω.1 j.succ) ^ 2 ≤ (Real.sin θ) ^ 2 := by
          have h1 : 1 - (ω.1 0) ^ 2 ≤ 1 - (Real.cos θ) ^ 2 := by
            nlinarith [hcos_nn, hω0_ge]
          have h2 : (Real.sin θ) ^ 2 = 1 - (Real.cos θ) ^ 2 := by
            nlinarith [Real.sin_sq_add_cos_sq θ]
          linarith
        have hsin_sq : (Real.sin θ) ^ 2 ≤ θ ^ 2 := by
          have habs := Real.abs_sin_le_abs (x := θ)
          rw [abs_of_pos hθ_pos] at habs
          nlinarith [abs_nonneg (Real.sin θ), sq_abs (Real.sin θ)]
        have hr_sq_le : r ^ 2 ≤ 1 := by nlinarith [hr.1, hr.2]
        have htail_nn : 0 ≤ ∑ j : Fin m, (ω.1 j.succ) ^ 2 :=
          Finset.sum_nonneg fun _ _ => sq_nonneg _
        nlinarith [sq_nonneg r]
      have hnorm_le : ‖WithLp.toLp 2 (fun j : Fin m => (r • ω.1) j.succ)‖ ≤ θ := by
        rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq hθ_pos.le]
        exact Real.sqrt_le_sqrt hnorm_sq
      linarith
  have hbot_sub : (splitE_nd m) ⁻¹' box_bot ⊆ Metric.ball (0 : E (m + 1)) 1 := by
    intro y hy
    rcases hy with ⟨hy0, hy_perp⟩
    rw [Set.mem_Ioo] at hy0
    rw [Metric.mem_ball, dist_zero_right] at hy_perp ⊢
    change (-1 / 2 : ℝ) < y 0 ∧ y 0 < 1 / 2 at hy0
    change ‖WithLp.toLp 2 (fun j : Fin m => y j.succ)‖ < Real.sqrt 3 / 2 at hy_perp
    have hnorm_sq : ‖y‖ ^ 2 < 1 := by
      have h1 : ‖y‖ ^ 2 = (y 0) ^ 2 + ‖WithLp.toLp 2 (fun j : Fin m => y j.succ)‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
      have hsq0 : (y 0) ^ 2 < 1 / 4 := by nlinarith [hy0.1, hy0.2]
      have hsqp : ‖WithLp.toLp 2 (fun j : Fin m => y j.succ)‖ ^ 2 < (Real.sqrt 3 / 2) ^ 2 := by
        have hlt : ‖WithLp.toLp 2 (fun j : Fin m => y j.succ)‖ < Real.sqrt 3 / 2 := hy_perp
        nlinarith [norm_nonneg (WithLp.toLp 2 (fun j : Fin m => y j.succ))]
      have hsqrt3 : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
        rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
      linarith
    rw [← Real.sqrt_sq (norm_nonneg y), ← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) hnorm_sq
  have hmeas_box_top : MeasurableSet box_top := measurableSet_Ico.prod measurableSet_ball
  have hmeas_box_bot : MeasurableSet box_bot := measurableSet_Ioo.prod measurableSet_ball
  have hnum_le : (volume : Measure (E (m + 1))).real sec ≤
      ((volume : Measure ℝ).prod (volume : Measure (E m))).real box_top := by
    have h1 : (volume : Measure (E (m + 1))) sec ≤
        (volume : Measure (E (m + 1))) ((splitE_nd m) ⁻¹' box_top) := measure_mono hsec_sub
    rw [hmp_vol.measure_preimage hmeas_box_top.nullMeasurableSet] at h1
    have htop_ne : ((volume : Measure ℝ).prod (volume : Measure (E m))) box_top ≠ ⊤ := by
      rw [Measure.prod_prod]
      refine ENNReal.mul_ne_top ?_ (measure_ball_lt_top (μ := (volume : Measure (E m)))).ne
      rw [Real.volume_Ico]
      exact ENNReal.ofReal_ne_top
    exact ENNReal.toReal_mono htop_ne h1
  have hden_ge : ((volume : Measure ℝ).prod (volume : Measure (E m))).real box_bot ≤
      (volume : Measure (E (m + 1))).real (Metric.ball (0 : E (m + 1)) 1) := by
    have h1 : (volume : Measure (E (m + 1))) ((splitE_nd m) ⁻¹' box_bot) ≤
        (volume : Measure (E (m + 1))) (Metric.ball (0 : E (m + 1)) 1) := measure_mono hbot_sub
    rw [hmp_vol.measure_preimage hmeas_box_bot.nullMeasurableSet] at h1
    exact ENNReal.toReal_mono (measure_ball_lt_top (μ := (volume : Measure (E (m + 1))))).ne h1
  have hbox_top_real : ((volume : Measure ℝ).prod (volume : Measure (E m))).real box_top =
      ((5 / 4 : ℝ) * θ) ^ m * (volume : Measure (E m)).real (Metric.ball (0 : E m) 1) := by
    rw [Measure.real, Measure.prod_prod, ENNReal.toReal_mul, Real.volume_Ico, sub_zero,
      ENNReal.toReal_ofReal (by norm_num), one_mul,
      (volume : Measure (E m)).addHaar_ball_of_pos 0 (by positivity),
      finrank_euclideanSpace_fin, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
    rfl
  have hbox_bot_real : ((volume : Measure ℝ).prod (volume : Measure (E m))).real box_bot =
      (Real.sqrt 3 / 2) ^ m * (volume : Measure (E m)).real (Metric.ball (0 : E m) 1) := by
    rw [Measure.real, Measure.prod_prod, ENNReal.toReal_mul, Real.volume_Ioo,
      show (1 / 2 : ℝ) - (-1 / 2 : ℝ) = 1 by norm_num,
      ENNReal.toReal_ofReal (by norm_num), one_mul,
      (volume : Measure (E m)).addHaar_ball_of_pos 0 (by positivity),
      finrank_euclideanSpace_fin, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
    rfl
  have hball_m_pos : 0 < (volume : Measure (E m)).real (Metric.ball (0 : E m) 1) := by
    rw [Measure.real, ENNReal.toReal_pos_iff]
    exact ⟨Metric.isOpen_ball.measure_pos _ ⟨0, Metric.mem_ball_self (x := (0 : E m)) one_pos⟩,
      MeasureTheory.measure_ball_lt_top⟩
  have hbot_pos : 0 < ((volume : Measure ℝ).prod (volume : Measure (E m))).real box_bot := by
    rw [hbox_bot_real]
    exact mul_pos (pow_pos (by positivity) m) hball_m_pos
  calc (volume : Measure (E (m + 1))).real sec /
        (volume : Measure (E (m + 1))).real (Metric.ball (0 : E (m + 1)) 1)
      ≤ ((volume : Measure ℝ).prod (volume : Measure (E m))).real box_top /
          ((volume : Measure ℝ).prod (volume : Measure (E m))).real box_bot :=
        div_le_div₀ (by positivity) hnum_le hbot_pos hden_ge
    _ = (((5 / 4 : ℝ) * θ) ^ m * (volume : Measure (E m)).real (Metric.ball (0 : E m) 1)) /
          ((Real.sqrt 3 / 2) ^ m * (volume : Measure (E m)).real (Metric.ball (0 : E m) 1)) := by
        rw [hbox_top_real, hbox_bot_real]
    _ = (((5 / 4 : ℝ) * θ) / (Real.sqrt 3 / 2)) ^ m := by
        rw [mul_div_mul_right _ _ hball_m_pos.ne', ← div_pow]
    _ ≤ (2 * θ) ^ m := by
        refine pow_le_pow_left₀ (by positivity) ?_ m
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.sqrt 3 / 2)]
        have hsqrt3 : 5 ≤ 4 * Real.sqrt 3 := by
          nlinarith only [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
        nlinarith only [hsqrt3, hθ_pos]
    _ = (2 * θ) ^ ((m + 1) - 1) := by rw [Nat.add_sub_cancel]

/-! ### Spherical Polynomial Subspace `V_d`, Dimension Bound, & `O(n)`-Invariance -/

def monom {n : ℕ} (α : Fin n → ℕ) (g : E n) : ℝ :=
  ∏ i : Fin n, (g i) ^ (α i)

noncomputable def M_d (n d : ℕ) : Submodule ℝ (E n → ℝ) :=
  Submodule.span ℝ (Set.image (monom : (Fin n → ℕ) → E n → ℝ) (I_deg n d : Set (Fin n → ℕ)))

lemma M_d_mono {n d₁ d₂ : ℕ} (h : d₁ ≤ d₂) : M_d n d₁ ≤ M_d n d₂ := by
  refine Submodule.span_mono (Set.image_mono ?_)
  intro α hα
  exact mem_I_deg.mpr ((mem_I_deg.mp hα).trans h)

lemma mul_coord_pow_mem_M_d {n d k : ℕ} (i₀ : Fin n) {f : E n → ℝ} (hf : f ∈ M_d n d) :
    (fun g : E n => (g i₀) ^ k * f g) ∈ M_d n (d + k) := by
  induction hf using Submodule.span_induction with
  | mem p hp =>
    rcases hp with ⟨β, hβ, rfl⟩
    have hβ_deg : totalDeg β ≤ d := mem_I_deg.mp hβ
    have hfn : (fun g : E n => (g i₀) ^ k * monom β g) =
        monom (Function.update β i₀ (β i₀ + k)) := by
      ext g
      have h1 : monom β g = (g i₀) ^ (β i₀) *
          ∏ i ∈ Finset.univ.erase i₀, (g i) ^ (β i) := by
        rw [monom, ← Finset.mul_prod_erase Finset.univ (fun i => (g i) ^ (β i)) (Finset.mem_univ i₀)]
      have h2 : monom (Function.update β i₀ (β i₀ + k)) g =
          (g i₀) ^ (β i₀ + k) * ∏ i ∈ Finset.univ.erase i₀, (g i) ^ (β i) := by
        rw [monom, ← Finset.mul_prod_erase Finset.univ
          (fun i => (g i) ^ (Function.update β i₀ (β i₀ + k) i)) (Finset.mem_univ i₀)]
        simp only [Function.update_self]
        congr 1
        refine Finset.prod_congr rfl fun i hi => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      rw [h1, h2, pow_add]
      ring
    rw [hfn]
    refine Submodule.subset_span ⟨Function.update β i₀ (β i₀ + k), mem_I_deg.mpr ?_, rfl⟩
    have hdeg1 : totalDeg (Function.update β i₀ (β i₀ + k)) = totalDeg β + k := by
      unfold totalDeg
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i₀),
        ← Finset.add_sum_erase Finset.univ β (Finset.mem_univ i₀)]
      simp only [Function.update_self]
      have hs : ∑ i ∈ Finset.univ.erase i₀, Function.update β i₀ (β i₀ + k) i =
          ∑ i ∈ Finset.univ.erase i₀, β i :=
        Finset.sum_congr rfl fun i hi => Function.update_of_ne (Finset.ne_of_mem_erase hi) _ β
      rw [hs]; omega
    omega
  | zero =>
    have h0 : (fun g : E n => (g i₀) ^ k * (0 : E n → ℝ) g) = 0 := by ext; simp
    rw [h0]
    exact (M_d n (d + k)).zero_mem
  | add x y _ _ ihx ihy =>
    have hadd : (fun g : E n => (g i₀) ^ k * (x + y) g) =
        (fun g => (g i₀) ^ k * x g) + (fun g => (g i₀) ^ k * y g) := by
      ext g; simp [mul_add]
    rw [hadd]
    exact (M_d n (d + k)).add_mem ihx ihy
  | smul c x _ ihx =>
    have hsm : (fun g : E n => (g i₀) ^ k * (c • x) g) = c • (fun g => (g i₀) ^ k * x g) := by
      ext g; simp [smul_eq_mul]; ring
    rw [hsm]
    exact (M_d n (d + k)).smul_mem c ihx

lemma mul_poly_coord_mem_M_d {n d : ℕ} (P : ℝ[X]) (m : ℕ) (hdeg : P.natDegree ≤ m)
    (i₀ : Fin n) {f : E n → ℝ} (hf : f ∈ M_d n d) :
    (fun g : E n => P.eval (g i₀) * f g) ∈ M_d n (d + m) := by
  have heq : (fun g : E n => P.eval (g i₀) * f g) =
      ∑ k ∈ Finset.range (m + 1), P.coeff k • (fun g => (g i₀) ^ k * f g) := by
    ext g
    rw [Polynomial.eval_eq_sum_range' (lt_of_le_of_lt hdeg (Nat.lt_succ_self m)), Finset.sum_mul]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [heq]
  refine Submodule.sum_mem _ fun k hk => ?_
  have hk_le : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  exact Submodule.smul_mem _ _ (M_d_mono (by omega) (mul_coord_pow_mem_M_d i₀ hf))

lemma Hnd_mem_M_d {n : ℕ} (α : Fin n → ℕ) : Hnd α ∈ M_d n (totalDeg α) := by
  have hu : ∀ i : Fin n, ∃ P : ℝ[X], P.natDegree ≤ α i ∧ ∀ x, h1D (α i) x = P.eval x :=
    fun i => exists_poly_h1D (α i)
  choose P hPdeg hPeq using hu
  have hone : (fun _ : E n => (1 : ℝ)) ∈ M_d n 0 := by
    have h0 : (fun _ : E n => (1 : ℝ)) = monom (0 : Fin n → ℕ) := by ext g; simp [monom]
    rw [h0]
    exact Submodule.subset_span ⟨0, mem_I_deg.mpr (by simp [totalDeg]), rfl⟩
  have hprod : ∀ s : Finset (Fin n),
      (fun g : E n => ∏ i ∈ s, h1D (α i) (g i)) ∈ M_d n (∑ i ∈ s, α i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hone
    | @insert i s hi ih =>
      have heq : (fun g : E n => ∏ j ∈ insert i s, h1D (α j) (g j)) =
          fun g => (P i).eval (g i) * (∏ j ∈ s, h1D (α j) (g j)) := by
        ext g
        rw [Finset.prod_insert hi, hPeq i]
      rw [heq, Finset.sum_insert hi, add_comm]
      exact mul_poly_coord_mem_M_d (P i) (α i) (hPdeg i) i ih
  have heq : Hnd α = fun g => ∏ i, h1D (α i) (g i) := by ext g; rfl
  have hdeg : totalDeg α = ∑ i, α i := rfl
  rw [heq, hdeg]
  exact hprod Finset.univ

lemma P_Hnd_le_M_d (n d : ℕ) : P_Hnd n d ≤ M_d n d := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨α, hα, rfl⟩
  exact M_d_mono (mem_I_deg.mp hα) (Hnd_mem_M_d α)

lemma monom_comp_smul_mem_M_d {n d : ℕ} (r : ℝ) (α : Fin n → ℕ) (hα : totalDeg α ≤ d) :
    (fun g : E n => monom α (r • g)) ∈ M_d n d := by
  have heq : (fun g : E n => monom α (r • g)) = (r ^ totalDeg α) • monom α := by
    ext g
    simp only [monom, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, totalDeg]
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, mem_I_deg.mpr hα, rfl⟩)

lemma M_d_comp_smul {n d : ℕ} (r : ℝ) {p : E n → ℝ} (hm : p ∈ M_d n d) :
    (fun g : E n => p (r • g)) ∈ M_d n d := by
  induction hm using Submodule.span_induction with
  | mem q hq =>
    rcases hq with ⟨α, hα, rfl⟩
    exact monom_comp_smul_mem_M_d r α (mem_I_deg.mp hα)
  | zero =>
    have h0 : (fun g : E n => (0 : E n → ℝ) (r • g)) = 0 := rfl
    rw [h0]
    exact (M_d n d).zero_mem
  | add x y _ _ ihx ihy =>
    have hadd : (fun g : E n => (x + y) (r • g)) =
        (fun g => x (r • g)) + (fun g => y (r • g)) := rfl
    rw [hadd]
    exact (M_d n d).add_mem ihx ihy
  | smul c x _ ihx =>
    have hsm : (fun g : E n => (c • x) (r • g)) = c • (fun g => x (r • g)) := rfl
    rw [hsm]
    exact (M_d n d).smul_mem c ihx

lemma P_Hnd_comp_smul {n d : ℕ} (r : ℝ) {p : E n → ℝ} (hp : p ∈ P_Hnd n d) :
    (fun g : E n => p (r • g)) ∈ M_d n d :=
  M_d_comp_smul r (P_Hnd_le_M_d n d hp)

noncomputable def restrictSphere (n : ℕ) : (E n → ℝ) →ₗ[ℝ] (Metric.sphere (0 : E n) 1 → ℝ) where
  toFun p ω := p ω.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def V_d (n d : ℕ) : Submodule ℝ (Metric.sphere (0 : E n) 1 → ℝ) :=
  Submodule.map (restrictSphere n) (M_d n d)

lemma P_Hnd_restrict_mem_V_d {n d : ℕ} {p : E n → ℝ} (hp : p ∈ P_Hnd n d) :
    restrictSphere n p ∈ V_d n d :=
  Submodule.mem_map_of_mem (P_Hnd_le_M_d n d hp)

lemma card_I_deg_le (k d : ℕ) : (I_deg k d).card ≤ Nat.choose (d + k) k := by
  induction k generalizing d with
  | zero =>
    have hsub : I_deg 0 d ⊆ Finset.univ := Finset.subset_univ _
    have hcard : (I_deg 0 d).card ≤ Fintype.card (Fin 0 → ℕ) :=
      (Finset.card_le_card hsub).trans (by simp)
    simp only [Nat.choose_zero_right] at hcard ⊢
    exact hcard.trans (by simp)
  | succ k ihk =>
    induction d with
    | zero =>
      have hsub : I_deg (k + 1) 0 ⊆ {(0 : Fin (k + 1) → ℕ)} := by
        intro β hβ
        rw [mem_I_deg] at hβ
        rw [Finset.mem_singleton]
        ext i
        have hle : β i ≤ totalDeg β :=
          Finset.single_le_sum (fun j _ => Nat.zero_le (β j)) (Finset.mem_univ i)
        simp only [Pi.zero_apply]
        omega
      calc (I_deg (k + 1) 0).card ≤ ({(0 : Fin (k + 1) → ℕ)} : Finset _).card :=
            Finset.card_le_card hsub
        _ = 1 := Finset.card_singleton _
        _ = Nat.choose (0 + (k + 1)) (k + 1) := by simp
    | succ d ihd =>
      let S0 := (I_deg (k + 1) (d + 1)).filter (fun β => β 0 = 0)
      let S1 := (I_deg (k + 1) (d + 1)).filter (fun β => β 0 ≠ 0)
      have hcard_eq : (I_deg (k + 1) (d + 1)).card ≤ S0.card + S1.card := by
        refine (Finset.card_le_card fun β hβ => ?_).trans (Finset.card_union_le S0 S1)
        by_cases h0 : β 0 = 0
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hβ, h0⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hβ, h0⟩)
      have hS0_le : S0.card ≤ (I_deg k (d + 1)).card := by
        refine Finset.card_le_card_of_injOn (fun β j => β j.succ) ?_ ?_
        · intro β hβ
          rw [Finset.mem_coe, Finset.mem_filter, mem_I_deg] at hβ
          rw [Finset.mem_coe, mem_I_deg]
          unfold totalDeg at hβ ⊢
          rw [Fin.sum_univ_succ, hβ.2, zero_add] at hβ
          exact hβ.1
        · intro β₁ hβ₁ β₂ hβ₂ heq
          rw [Finset.mem_coe, Finset.mem_filter] at hβ₁ hβ₂
          ext i
          cases i using Fin.cases with
          | zero => rw [hβ₁.2, hβ₂.2]
          | succ j => exact congrFun heq j
      have hS1_le : S1.card ≤ (I_deg (k + 1) d).card := by
        refine Finset.card_le_card_of_injOn (fun β => Function.update β 0 (β 0 - 1)) ?_ ?_
        · intro β hβ
          rw [Finset.mem_coe, Finset.mem_filter, mem_I_deg] at hβ
          rw [Finset.mem_coe, mem_I_deg]
          have hpos : 1 ≤ β 0 := Nat.pos_of_ne_zero hβ.2
          unfold totalDeg at hβ ⊢
          rw [Fin.sum_univ_succ] at hβ ⊢
          simp only [Function.update_self]
          have hs : ∑ j : Fin k, Function.update β 0 (β 0 - 1) j.succ =
              ∑ j : Fin k, β j.succ :=
            Finset.sum_congr rfl fun j _ => Function.update_of_ne (Fin.succ_ne_zero j) _ β
          rw [hs]
          omega
        · intro β₁ hβ₁ β₂ hβ₂ heq
          rw [Finset.mem_coe, Finset.mem_filter] at hβ₁ hβ₂
          have h1 : 1 ≤ β₁ 0 := Nat.pos_of_ne_zero hβ₁.2
          have h2 : 1 ≤ β₂ 0 := Nat.pos_of_ne_zero hβ₂.2
          ext i
          cases i using Fin.cases with
          | zero =>
            have h0 := congrFun heq 0
            simp only [Function.update_self] at h0
            omega
          | succ j =>
            have hj := congrFun heq j.succ
            simpa [Function.update_of_ne (Fin.succ_ne_zero j)] using hj
      calc (I_deg (k + 1) (d + 1)).card
          ≤ S0.card + S1.card := hcard_eq
        _ ≤ (I_deg k (d + 1)).card + (I_deg (k + 1) d).card := add_le_add hS0_le hS1_le
        _ ≤ Nat.choose (d + 1 + k) k + Nat.choose (d + (k + 1)) (k + 1) :=
            add_le_add (ihk (d + 1)) ihd
        _ = Nat.choose (d + 1 + (k + 1)) (k + 1) := by
            rw [show d + 1 + (k + 1) = (d + k + 1) + 1 by omega,
              show d + 1 + k = d + k + 1 by omega,
              show d + (k + 1) = d + k + 1 by omega,
              Nat.choose_succ_succ (d + k + 1) k, add_comm]

lemma choose_add_le_exp (d m : ℕ) (hm : 1 ≤ m) :
    (Nat.choose (d + m) m : ℝ) ≤ (Real.exp 1 * (1 + (d : ℝ) / m)) ^ m := by
  have hm_pos : (0 : ℝ) < m := by positivity
  have hdesc : ∀ k : ℕ, (Nat.descFactorial (d + m) k : ℝ) ≤ ((d + m : ℝ)) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.descFactorial_succ, Nat.cast_mul, pow_succ']
      refine mul_le_mul ?_ ih (by positivity) (by positivity)
      have hle : d + m - k ≤ d + m := Nat.sub_le _ _
      exact_mod_cast hle
  have hfac_choose : (Nat.choose (d + m) m : ℝ) * (m.factorial : ℝ) =
      (Nat.descFactorial (d + m) m : ℝ) := by
    exact_mod_cast (mul_comm (Nat.choose (d + m) m) m.factorial).trans
      (Nat.descFactorial_eq_factorial_mul_choose (d + m) m).symm
  have hpow_exp : ((m : ℝ) ^ m) / (m.factorial : ℝ) ≤ Real.exp m := by
    have hsum := Real.sum_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ m) (m + 1)
    have hmem : m ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_self m)
    exact (Finset.single_le_sum (fun k _ => by positivity) hmem).trans hsum
  have hexp_m : Real.exp (m : ℝ) = (Real.exp 1) ^ m := by
    rw [← Real.exp_nat_mul, mul_one]
  rw [hexp_m] at hpow_exp
  have hfac_pos : (0 : ℝ) < m.factorial := by positivity
  have hpow_pos : (0 : ℝ) < (m : ℝ) ^ m := by positivity
  have hinv_le : (m.factorial : ℝ)⁻¹ ≤ (Real.exp 1 / (m : ℝ)) ^ m := by
    rw [div_pow, le_div_iff₀ hpow_pos, inv_mul_eq_div]
    exact hpow_exp
  calc (Nat.choose (d + m) m : ℝ)
      = (Nat.descFactorial (d + m) m : ℝ) * (m.factorial : ℝ)⁻¹ := by
        rw [← hfac_choose, mul_inv_cancel_right₀ hfac_pos.ne']
    _ ≤ ((d + m : ℝ)) ^ m * (Real.exp 1 / (m : ℝ)) ^ m :=
        mul_le_mul (hdesc m) hinv_le (by positivity) (by positivity)
    _ = ((d + m : ℝ) * (Real.exp 1 / (m : ℝ))) ^ m := by rw [mul_pow]
    _ = (Real.exp 1 * (1 + (d : ℝ) / m)) ^ m := by
        congr 1
        field_simp
        ring

lemma finrank_V_d_le {n : ℕ} (hn : 2 ≤ n) (d : ℕ) :
    (Module.finrank ℝ (V_d n d) : ℝ) ≤
      2 * (Real.exp 1 * (1 + (d : ℝ) / (n - 1))) ^ (n - 1) := by
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨m, rfl⟩
  have hm : 1 ≤ m := by omega
  let gen : Bool × I_deg m d → Metric.sphere (0 : E (m + 1)) 1 → ℝ :=
    fun p ω => (ω.1 0) ^ (if p.1 then 1 else 0) * ∏ j : Fin m, (ω.1 j.succ) ^ (p.2.1 j)
  let redSpan : Submodule ℝ (Metric.sphere (0 : E (m + 1)) 1 → ℝ) :=
    Submodule.span ℝ (Set.range gen)
  have hmonom_in : ∀ α : Fin (m + 1) → ℕ, totalDeg α ≤ d →
      restrictSphere (m + 1) (monom α) ∈ redSpan := by
    intro α hα
    have hstrong : ∀ k : ℕ, ∀ α : Fin (m + 1) → ℕ, α 0 ≤ k → totalDeg α ≤ d →
        restrictSphere (m + 1) (monom α) ∈ redSpan := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
        intro α hα0 hdeg
        rcases le_or_gt (α 0) 1 with h01 | hge2
        · let b : Bool := decide (α 0 = 1)
          let β : Fin m → ℕ := fun j => α j.succ
          have hβ_deg : totalDeg β ≤ d := by
            unfold totalDeg at *
            rw [Fin.sum_univ_succ] at hdeg
            dsimp only [β]
            omega
          let p : Bool × I_deg m d := (b, ⟨β, mem_I_deg.mpr hβ_deg⟩)
          have heq : restrictSphere (m + 1) (monom α) = gen p := by
            ext ω
            simp only [restrictSphere, LinearMap.coe_mk, AddHom.coe_mk, monom,
              Fin.prod_univ_succ, gen, p, b, β]
            have hpow0 : (if decide (α 0 = 1) then 1 else 0) = α 0 := by
              by_cases h1 : α 0 = 1
              · simp [h1]
              · simp [h1]; omega
            rw [hpow0]
          rw [heq]
          exact Submodule.subset_span ⟨p, rfl⟩
        · have hα0_ge2 : 2 ≤ α 0 := hge2
          let α_rem : Fin (m + 1) → ℕ := Function.update α 0 (α 0 - 2)
          let α_j : Fin m → Fin (m + 1) → ℕ := fun j =>
            Function.update α_rem j.succ (α_rem j.succ + 2)
          have hrem_deg : totalDeg α_rem ≤ d := by
            unfold totalDeg at *
            rw [Fin.sum_univ_succ] at hdeg
            rw [Fin.sum_univ_succ]
            simp only [α_rem, Function.update_self]
            have hs : ∑ j : Fin m, Function.update α 0 (α 0 - 2) j.succ =
                ∑ j : Fin m, α j.succ :=
              Finset.sum_congr rfl fun j _ => Function.update_of_ne (Fin.succ_ne_zero j) _ α
            rw [hs]; omega
          have hj_deg : ∀ j : Fin m, totalDeg (α_j j) ≤ d := by
            intro j
            unfold totalDeg at *
            rw [Fin.sum_univ_succ] at hdeg
            have h1 : ∑ i : Fin (m + 1), α_j j i = (∑ i : Fin (m + 1), α_rem i) + 2 := by
              rw [← Finset.add_sum_erase Finset.univ (α_j j) (Finset.mem_univ j.succ),
                ← Finset.add_sum_erase Finset.univ α_rem (Finset.mem_univ j.succ)]
              simp only [α_j, Function.update_self]
              have hs : ∑ i ∈ Finset.univ.erase j.succ,
                    Function.update α_rem j.succ (α_rem j.succ + 2) i =
                  ∑ i ∈ Finset.univ.erase j.succ, α_rem i :=
                Finset.sum_congr rfl fun i hi =>
                  Function.update_of_ne (Finset.ne_of_mem_erase hi) _ α_rem
              rw [hs]; omega
            have h2 : (∑ i : Fin (m + 1), α_rem i) + 2 = α 0 + ∑ i : Fin m, α i.succ := by
              rw [Fin.sum_univ_succ]
              simp only [α_rem, Function.update_self]
              have hs : ∑ j' : Fin m, Function.update α 0 (α 0 - 2) j'.succ =
                  ∑ j' : Fin m, α j'.succ :=
                Finset.sum_congr rfl fun j' _ => Function.update_of_ne (Fin.succ_ne_zero j') _ α
              rw [hs]; omega
            omega
          have hdecomp : restrictSphere (m + 1) (monom α) =
              restrictSphere (m + 1) (monom α_rem) -
                ∑ j : Fin m, restrictSphere (m + 1) (monom (α_j j)) := by
            ext ω
            have hω_norm : ‖ω.1‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
            have hsum_ω : (ω.1 0) ^ 2 = 1 - ∑ j : Fin m, (ω.1 j.succ) ^ 2 := by
              have h1 := EuclideanSpace.real_norm_sq_eq ω.1
              rw [hω_norm, one_pow, Fin.sum_univ_succ] at h1
              linarith
            have hrem_eval : monom α_rem ω.1 =
                (ω.1 0) ^ (α 0 - 2) * ∏ j : Fin m, (ω.1 j.succ) ^ (α j.succ) := by
              rw [monom, Fin.prod_univ_succ]
              simp [α_rem]
            have hj_eval : ∀ j : Fin m, monom (α_j j) ω.1 =
                (ω.1 j.succ) ^ 2 * monom α_rem ω.1 := by
              intro j
              rw [monom, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j.succ)]
              simp only [α_j, Function.update_self, pow_add]
              have hprod_rem : monom α_rem ω.1 =
                  (ω.1 j.succ) ^ (α_rem j.succ) *
                    ∏ i ∈ Finset.univ.erase j.succ, (ω.1 i) ^ (α_rem i) := by
                rw [monom, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j.succ)]
              have hs : ∏ i ∈ Finset.univ.erase j.succ,
                    (ω.1 i) ^ (Function.update α_rem j.succ (α_rem j.succ + 2) i) =
                  ∏ i ∈ Finset.univ.erase j.succ, (ω.1 i) ^ (α_rem i) :=
                Finset.prod_congr rfl fun i hi => by
                  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
              rw [hs, hprod_rem]
              ring
            simp only [restrictSphere, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply,
              Finset.sum_apply]
            have hpow_split : α 0 = (α 0 - 2) + 2 := by omega
            have hα_eval : monom α ω.1 = (ω.1 0) ^ 2 * monom α_rem ω.1 := by
              rw [monom, Fin.prod_univ_succ, hrem_eval]
              conv_lhs => rw [hpow_split, pow_add]
              ring
            rw [hα_eval, hsum_ω, sub_mul, one_mul, Finset.sum_mul]
            congr 1
            refine Finset.sum_congr rfl fun j _ => (hj_eval j).symm
          rw [hdecomp]
          have hk0 : α 0 - 2 < k := by omega
          have hrem_mem := ih (α 0 - 2) hk0 α_rem (by simp [α_rem]) hrem_deg
          have hj_mem : ∀ j : Fin m, restrictSphere (m + 1) (monom (α_j j)) ∈ redSpan := by
            intro j
            have h0_eq : α_j j 0 = α 0 - 2 := by
              dsimp [α_j]
              rw [Function.update_of_ne (Fin.succ_ne_zero j).symm]
              simp [α_rem]
            exact ih (α 0 - 2) hk0 (α_j j) h0_eq.le (hj_deg j)
          exact redSpan.sub_mem hrem_mem (Submodule.sum_mem _ fun j _ => hj_mem j)
    exact hstrong (α 0) α le_rfl hα
  have hle_red : V_d (m + 1) d ≤ redSpan := by
    rw [V_d, M_d, Submodule.map_span_le]
    rintro _ ⟨α, hα, rfl⟩
    exact hmonom_in α (mem_I_deg.mp hα)
  have : Finite (Set.range gen) := Set.finite_range gen
  let _inst : Fintype (Set.range gen) := Fintype.ofFinite (Set.range gen)
  have : Module.Finite ℝ redSpan := FiniteDimensional.span_of_finite ℝ (Set.finite_range gen)
  have hfin_red : Module.finrank ℝ redSpan ≤ Fintype.card (Bool × I_deg m d) :=
    (finrank_span_le_card (Set.range gen)).trans_eq (Set.toFinset_card _) |>.trans
      (Fintype.card_range_le gen)
  have hfin_V : Module.finrank ℝ (V_d (m + 1) d) ≤ 2 * Nat.choose (d + m) m := by
    calc Module.finrank ℝ (V_d (m + 1) d)
        ≤ Module.finrank ℝ redSpan := Submodule.finrank_mono hle_red
      _ ≤ Fintype.card (Bool × I_deg m d) := hfin_red
      _ = 2 * (I_deg m d).card := by simp [Fintype.card_prod]
      _ ≤ 2 * Nat.choose (d + m) m := Nat.mul_le_mul_left 2 (card_I_deg_le m d)
  have hcast : (Module.finrank ℝ (V_d (m + 1) d) : ℝ) ≤ (2 : ℝ) * (Nat.choose (d + m) m : ℝ) := by
    exact_mod_cast hfin_V
  refine hcast.trans ?_
  have hc := choose_add_le_exp d m hm
  have hmul : (2 : ℝ) * (Nat.choose (d + m) m : ℝ) ≤
      (2 : ℝ) * (Real.exp 1 * (1 + (d : ℝ) / m)) ^ m :=
    mul_le_mul_of_nonneg_left hc (by norm_num)
  have hm1 : m.succ - 1 = m := Nat.succ_sub_one m
  have hm2 : (m.succ : ℝ) - 1 = m := by simp
  rw [hm1, hm2]
  exact hmul

/-! ### Continuous Orthonormal Basis of `V_d` & `O(n)`-Invariance -/

lemma continuous_of_mem_M_d {n d : ℕ} {p : E n → ℝ} (hp : p ∈ M_d n d) : Continuous p := by
  induction hp using Submodule.span_induction with
  | mem q hq =>
    rcases hq with ⟨α, _, rfl⟩
    unfold monom
    exact continuous_finsetProd _ fun i _ => (PiLp.continuous_apply 2 (fun _ => ℝ) i).pow (α i)
  | zero => exact continuous_zero
  | add x y _ _ ihx ihy => exact ihx.add ihy
  | smul c x _ ihx => exact continuous_const.mul ihx

lemma continuous_of_mem_V_d {n d : ℕ} {p : Metric.sphere (0 : E n) 1 → ℝ} (hp : p ∈ V_d n d) :
    Continuous p := by
  rcases Submodule.mem_map.mp hp with ⟨q, hq, rfl⟩
  exact (continuous_of_mem_M_d hq).comp continuous_subtype_val

lemma memLp_of_mem_V_d {n : ℕ} (hn : 1 ≤ n) (d : ℕ)
    {p : Metric.sphere (0 : E n) 1 → ℝ} (hp : p ∈ V_d n d) : MemLp p 2 (μS n) := by
  have : IsProbabilityMeasure (μS n) := isProbabilityMeasure_μS hn
  have hc := continuous_of_mem_V_d hp
  have hcompact : IsCompact (Set.univ : Set (Metric.sphere (0 : E n) 1)) := isCompact_univ
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hc.continuousOn
  exact MemLp.of_bound hc.aestronglyMeasurable C (ae_of_all _ fun ω => hC ω (Set.mem_univ ω))

noncomputable def toSphereL2 {n : ℕ} (hn : 1 ≤ n) (d : ℕ) :
    V_d n d →ₗ[ℝ] Lp ℝ 2 (μS n) where
  toFun p := (memLp_of_mem_V_d hn d p.2).toLp p.1
  map_add' p q := by
    refine Lp.ext ?_
    filter_upwards [(memLp_of_mem_V_d hn d (p + q).2).coeFn_toLp,
      Lp.coeFn_add ((memLp_of_mem_V_d hn d p.2).toLp p.1) ((memLp_of_mem_V_d hn d q.2).toLp q.1),
      (memLp_of_mem_V_d hn d p.2).coeFn_toLp, (memLp_of_mem_V_d hn d q.2).coeFn_toLp] with
      ω hsum hadd hp hq
    change (memLp_of_mem_V_d hn d (p + q).2).toLp (p + q).1 ω = _
    rw [hsum, hadd, Pi.add_apply, hp, hq]
    rfl
  map_smul' c p := by
    refine Lp.ext ?_
    filter_upwards [(memLp_of_mem_V_d hn d (c • p).2).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_of_mem_V_d hn d p.2).toLp p.1),
      (memLp_of_mem_V_d hn d p.2).coeFn_toLp] with ω hsmul hcoe hp
    change (memLp_of_mem_V_d hn d (c • p).2).toLp (c • p).1 ω =
      ((c • (memLp_of_mem_V_d hn d p.2).toLp p.1 : Lp ℝ 2 (μS n)) : _ → ℝ) ω
    rw [hsmul, hcoe, Pi.smul_apply, hp]
    rfl

lemma toSphereL2_injective {n : ℕ} (hn : 1 ≤ n) (d : ℕ) :
    Function.Injective (toSphereL2 hn d) := by
  have : IsProbabilityMeasure (μS n) := isProbabilityMeasure_μS hn
  have : (μS n).IsOpenPosMeasure := isOpenPosMeasure_μS hn
  rw [injective_iff_map_eq_zero]
  intro p hp
  have hae : (p.1 : Metric.sphere (0 : E n) 1 → ℝ) =ᵐ[μS n] 0 := by
    have h0 := Lp.coeFn_zero ℝ 2 (μS n)
    have hcoe := (memLp_of_mem_V_d hn d p.2).coeFn_toLp
    rw [show (memLp_of_mem_V_d hn d p.2).toLp p.1 = toSphereL2 hn d p from rfl, hp] at hcoe
    exact hcoe.symm.trans h0
  have hsq0 : ∫ ω, (p.1 ω) ^ 2 ∂(μS n) = 0 := by
    calc ∫ ω, (p.1 ω) ^ 2 ∂(μS n)
        = ∫ _ : Metric.sphere (0 : E n) 1, (0 : ℝ) ∂(μS n) := by
          refine integral_congr_ae ?_
          filter_upwards [hae] with ω hω
          have hω0 : p.1 ω = 0 := hω
          simp [hω0]
      _ = 0 := by simp
  ext ω₀
  by_contra hne
  have hc := continuous_of_mem_V_d p.2
  have hsq_int : Integrable (fun ω => (p.1 ω) ^ 2) (μS n) := (memLp_of_mem_V_d hn d p.2).integrable_sq
  have hpos := integral_pos_of_integrable_nonneg_nonzero (hc.pow 2) hsq_int
    (fun ω => sq_nonneg _) (pow_ne_zero 2 hne)
  have hpos' : 0 < ∫ ω, (p.1 ω) ^ 2 ∂(μS n) := hpos
  linarith

lemma M_d_comp_isom {n d : ℕ} (R : E n ≃ₗᵢ[ℝ] E n) {p : E n → ℝ} (hp : p ∈ M_d n d) :
    (p ∘ R) ∈ M_d n d := by
  have hmon : ∀ (i₀ : Fin n) (f : E n → ℝ) (d' : ℕ), f ∈ M_d n d' →
      (fun g : E n => (R g) i₀ * f g) ∈ M_d n (d' + 1) := by
    intro i₀ f d' hf
    have heq : (fun g : E n => (R g) i₀ * f g) =
        ∑ j : Fin n, (R.symm (EuclideanSpace.basisFun (Fin n) ℝ i₀) j) •
          (fun g : E n => g j * f g) := by
      ext g
      have hcoord : (R g) i₀ =
          ∑ j : Fin n, (R.symm (EuclideanSpace.basisFun (Fin n) ℝ i₀) j) * g j := by
        rw [← EuclideanSpace.inner_basisFun_real (Fin n) (R g) i₀, R.inner_map_eq_flip,
          real_inner_comm, PiLp.inner_apply]
        refine Finset.sum_congr rfl fun j _ => by simp [RCLike.inner_apply, mul_comm]
      rw [hcoord, Finset.sum_mul]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [heq]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (by simpa using mul_coord_pow_mem_M_d (k := 1) j hf)
  induction hp using Submodule.span_induction with
  | mem q hq =>
    rcases hq with ⟨α, hα, rfl⟩
    have hone : (fun _ : E n => (1 : ℝ)) ∈ M_d n 0 := by
      have h0 : (fun _ : E n => (1 : ℝ)) = monom (0 : Fin n → ℕ) := by ext g; simp [monom]
      rw [h0]
      exact Submodule.subset_span ⟨0, mem_I_deg.mpr (by simp [totalDeg]), rfl⟩
    have hprod : ∀ s : Finset (Fin n),
        (fun g : E n => ∏ i ∈ s, ((R g) i) ^ (α i)) ∈ M_d n (∑ i ∈ s, α i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using hone
      | @insert i s hi ih =>
        have hstep : ∀ k : ℕ, ∀ f : E n → ℝ, ∀ d' : ℕ, f ∈ M_d n d' →
            (fun g : E n => ((R g) i) ^ k * f g) ∈ M_d n (d' + k) := by
          intro k
          induction k with
          | zero => intro f d' hf; simpa using hf
          | succ k ihk =>
            intro f d' hf
            have heq : (fun g : E n => ((R g) i) ^ (k + 1) * f g) =
                fun g => (R g) i * (((R g) i) ^ k * f g) := by ext g; ring
            rw [heq, ← add_assoc]
            exact hmon i _ _ (ihk f d' hf)
        have heq : (fun g : E n => ∏ j ∈ insert i s, ((R g) j) ^ (α j)) =
            fun g => ((R g) i) ^ (α i) * ∏ j ∈ s, ((R g) j) ^ (α j) := by
          ext g; rw [Finset.prod_insert hi]
        rw [heq, Finset.sum_insert hi, add_comm]
        exact hstep (α i) _ _ ih
    exact M_d_mono (mem_I_deg.mp hα) (by simpa [Function.comp_def, monom, totalDeg] using hprod Finset.univ)
  | zero => exact (M_d n d).zero_mem
  | add x y _ _ ihx ihy =>
    have hadd : ((x + y) ∘ R) = (x ∘ R) + (y ∘ R) := rfl
    rw [hadd]
    exact (M_d n d).add_mem ihx ihy
  | smul c x _ ihx =>
    have hsm : ((c • x) ∘ R) = c • (x ∘ R) := rfl
    rw [hsm]
    exact (M_d n d).smul_mem c ihx

lemma V_d_comp_sphereHomeo {n d : ℕ} (R : E n ≃ₗᵢ[ℝ] E n)
    {p : Metric.sphere (0 : E n) 1 → ℝ} (hp : p ∈ V_d n d) :
    (p ∘ sphereHomeo R) ∈ V_d n d := by
  rcases Submodule.mem_map.mp hp with ⟨q, hq, rfl⟩
  refine ⟨q ∘ R, M_d_comp_isom R hq, ?_⟩
  ext ω; rfl

lemma spherical_basis {n : ℕ} (hn : 2 ≤ n) (d : ℕ) :
    ∃ (D : ℕ) (phiS : Fin D → Metric.sphere (0 : E n) 1 → ℝ),
      D = Module.finrank ℝ (V_d n d) ∧
      (∀ i, phiS i ∈ V_d n d) ∧
      (∀ i j, ∫ ω, phiS i ω * phiS j ω ∂(μS n) = if i = j then 1 else 0) ∧
      (∀ p ∈ V_d n d, ∀ ω, p ω = ∑ j : Fin D, (∫ ω', phiS j ω' * p ω' ∂(μS n)) * phiS j ω) ∧
      (∀ ω, ∑ j : Fin D, (phiS j ω) ^ 2 = (D : ℝ)) := by
  have hn1 : 1 ≤ n := by omega
  have : IsProbabilityMeasure (μS n) := isProbabilityMeasure_μS hn1
  have : FiniteDimensional ℝ (M_d n d) :=
    FiniteDimensional.span_of_finite ℝ ((I_deg n d).finite_toSet.image monom)
  have : FiniteDimensional ℝ (V_d n d) := by
    rw [V_d, M_d, Submodule.map_span]
    exact FiniteDimensional.span_of_finite ℝ
      (((I_deg n d).finite_toSet.image monom).image (restrictSphere n))
  let fL2 := toSphereL2 hn1 d
  let W : Submodule ℝ (Lp ℝ 2 (μS n)) := LinearMap.range fL2
  have : FiniteDimensional ℝ W := fL2.finiteDimensional_range
  let D := Module.finrank ℝ (V_d n d)
  let e_lin : V_d n d ≃ₗ[ℝ] W := LinearEquiv.ofInjective fL2 (toSphereL2_injective hn1 d)
  have hDW : Module.finrank ℝ W = D := e_lin.symm.finrank_eq
  let b : OrthonormalBasis (Fin D) ℝ W := (stdOrthonormalBasis ℝ W).reindex (finCongr hDW)
  let phiV : Fin D → V_d n d := fun i => e_lin.symm (b i)
  let phiS : Fin D → Metric.sphere (0 : E n) 1 → ℝ := fun i => (phiV i).1
  have hphi_L2 : ∀ i, (fL2 (phiV i) : Lp ℝ 2 (μS n)) = (b i : Lp ℝ 2 (μS n)) := by
    intro i
    change ((e_lin (e_lin.symm (b i))) : Lp ℝ 2 (μS n)) = _
    rw [e_lin.apply_symm_apply]
  have hphi_ortho : ∀ i j, ∫ ω, phiS i ω * phiS j ω ∂(μS n) = if i = j then 1 else 0 := by
    intro i j
    have hin : inner ℝ (b i) (b j) = if i = j then 1 else 0 :=
      orthonormal_iff_ite.mp b.orthonormal i j
    change inner ℝ (b i : Lp ℝ 2 (μS n)) (b j : Lp ℝ 2 (μS n)) = _ at hin
    rw [← hphi_L2 i, ← hphi_L2 j, MeasureTheory.L2.inner_def] at hin
    have hae : (fun ω => inner ℝ (fL2 (phiV i) ω) (fL2 (phiV j) ω)) =ᵐ[μS n]
        fun ω => phiS i ω * phiS j ω := by
      filter_upwards [(memLp_of_mem_V_d hn1 d (phiV i).2).coeFn_toLp,
        (memLp_of_mem_V_d hn1 d (phiV j).2).coeFn_toLp] with ω hi hj
      change inner ℝ ((memLp_of_mem_V_d hn1 d (phiV i).2).toLp (phiV i).1 ω)
        ((memLp_of_mem_V_d hn1 d (phiV j).2).toLp (phiV j).1 ω) = _ at *
      rw [hi, hj]
      simp only [phiS, RCLike.inner_apply, conj_trivial]
      ring
    rwa [integral_congr_ae hae] at hin
  have hphi_span : ∀ p ∈ V_d n d, ∀ ω,
      p ω = ∑ j : Fin D, (∫ ω', phiS j ω' * p ω' ∂(μS n)) * phiS j ω := by
    intro p hp ω
    let pV : V_d n d := ⟨p, hp⟩
    let pW : W := e_lin pV
    have hrep := b.sum_repr pW
    have hcoef : ∀ j : Fin D, b.repr pW j = ∫ ω', phiS j ω' * p ω' ∂(μS n) := by
      intro j
      rw [b.repr_apply_apply]
      change inner ℝ (b j : Lp ℝ 2 (μS n)) (pW : Lp ℝ 2 (μS n)) = _
      rw [← hphi_L2 j, show (pW : Lp ℝ 2 (μS n)) = fL2 pV from rfl, MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [(memLp_of_mem_V_d hn1 d (phiV j).2).coeFn_toLp,
        (memLp_of_mem_V_d hn1 d hp).coeFn_toLp] with ω' hj hp'
      change inner ℝ ((memLp_of_mem_V_d hn1 d (phiV j).2).toLp (phiV j).1 ω')
        ((memLp_of_mem_V_d hn1 d hp).toLp p ω') = _
      rw [hj, hp']
      simp only [phiS, RCLike.inner_apply, conj_trivial]
      ring
    have hp_eq : pV = ∑ j : Fin D, (∫ ω', phiS j ω' * p ω' ∂(μS n)) • phiV j := by
      apply e_lin.injective
      rw [map_sum]
      simp_rw [map_smul, show ∀ j, e_lin (phiV j) = b j from fun j => e_lin.apply_symm_apply (b j),
        ← hcoef]
      exact hrep.symm
    have hval := congrArg (fun q : V_d n d => q.1 ω) hp_eq
    simpa [phiS, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hval
  have hsum_sq : ∀ ω : Metric.sphere (0 : E n) 1, ∑ j : Fin D, (phiS j ω) ^ 2 = (D : ℝ) := by
    have hconst : ∀ ω₁ ω₂ : Metric.sphere (0 : E n) 1,
        ∑ j : Fin D, (phiS j ω₁) ^ 2 = ∑ j : Fin D, (phiS j ω₂) ^ 2 := by
      intro ω₁ ω₂
      rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨m, rfl⟩
      have h1_norm : ‖ω₁.1‖ = 1 := mem_sphere_zero_iff_norm.mp ω₁.2
      have h2_norm : ‖ω₂.1‖ = 1 := mem_sphere_zero_iff_norm.mp ω₂.2
      obtain ⟨b₁, hb₁⟩ := exists_orthonormalBasis_zero ω₁.1 h1_norm
      obtain ⟨b₂, hb₂⟩ := exists_orthonormalBasis_zero ω₂.1 h2_norm
      let R : E (m + 1) ≃ₗᵢ[ℝ] E (m + 1) := b₁.equiv b₂ (Equiv.refl _)
      have hRω : sphereHomeo R ω₁ = ω₂ := by
        ext1; dsimp [sphereHomeo, R]; rw [← hb₁, OrthonormalBasis.equiv_apply_basis, Equiv.refl_apply, hb₂]
      let psiV : Fin D → V_d (m + 1) d := fun j => ⟨phiS j ∘ sphereHomeo R, V_d_comp_sphereHomeo R (phiV j).2⟩
      let psiW : Fin D → W := fun j => e_lin (psiV j)
      have hpsi_ortho : Orthonormal ℝ psiW := by
        rw [orthonormal_iff_ite]
        intro i j
        change inner ℝ (fL2 (psiV i)) (fL2 (psiV j)) = _
        rw [MeasureTheory.L2.inner_def]
        have hae : (fun ω => inner ℝ (fL2 (psiV i) ω) (fL2 (psiV j) ω)) =ᵐ[μS (m + 1)]
            fun ω => phiS i (sphereHomeo R ω) * phiS j (sphereHomeo R ω) := by
          filter_upwards [(memLp_of_mem_V_d hn1 d (psiV i).2).coeFn_toLp,
            (memLp_of_mem_V_d hn1 d (psiV j).2).coeFn_toLp] with ω hi hj
          change inner ℝ ((memLp_of_mem_V_d hn1 d (psiV i).2).toLp (psiV i).1 ω)
            ((memLp_of_mem_V_d hn1 d (psiV j).2).toLp (psiV j).1 ω) = _
          rw [hi, hj]
          simp only [psiV, Function.comp_def, RCLike.inner_apply, conj_trivial]
          ring
        rw [integral_congr_ae hae]
        have hmp_R : MeasurePreserving (sphereHomeo R) (μS (m + 1)) (μS (m + 1)) :=
          measurePreserving_sphereHomeo (by omega) R
        calc ∫ ω, phiS i (sphereHomeo R ω) * phiS j (sphereHomeo R ω) ∂(μS (m + 1))
            = ∫ ω, (fun ω' => phiS i ω' * phiS j ω') (sphereHomeo R ω) ∂(μS (m + 1)) := rfl
          _ = ∫ ω', phiS i ω' * phiS j ω' ∂(μS (m + 1)) :=
              hmp_R.integral_comp (sphereHomeo R).measurableEmbedding
                (fun ω' : Metric.sphere (0 : E (m + 1)) 1 => phiS i ω' * phiS j ω')
          _ = if i = j then 1 else 0 := hphi_ortho i j
      have hspan_top : ⊤ ≤ Submodule.span ℝ (Set.range psiW) := by
        refine Eq.ge (Submodule.eq_top_of_finrank_eq ?_)
        rw [finrank_span_eq_card hpsi_ortho.linearIndependent, Fintype.card_fin, hDW]
      let b_psi : OrthonormalBasis (Fin D) ℝ W := OrthonormalBasis.mk hpsi_ortho hspan_top
      have hb_eq : ∀ j, (b_psi j : W) = psiW j := fun j => by rw [OrthonormalBasis.coe_mk]
      have hpsi_exp : ∀ j ω, (psiV j).1 ω = ∑ k : Fin D, inner ℝ (b k) (b_psi j) * phiS k ω := by
        intro j ω
        have hW_eq : psiW j = ∑ k : Fin D, inner ℝ (b k) (b_psi j) • b k := by
          rw [← hb_eq j]
          simpa [b.repr_apply_apply] using (b.sum_repr (b_psi j)).symm
        have hV_eq : psiV j = ∑ k : Fin D, inner ℝ (b k) (b_psi j) • phiV k := by
          apply e_lin.injective
          rw [map_sum]
          simp_rw [map_smul, show ∀ k, e_lin (phiV k) = b k from fun k => e_lin.apply_symm_apply (b k)]
          exact hW_eq
        have hpt := congrArg (fun q : V_d (m + 1) d => q.1 ω) hV_eq
        simpa [phiS, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hpt
      have hsum_R : ∑ j : Fin D, (phiS j ω₂) ^ 2 = ∑ j : Fin D, ((psiV j).1 ω₁) ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [psiV, Function.comp_def, hRω]
      rw [hsum_R, eq_comm]
      simp_rw [hpsi_exp _ ω₁, sq, Finset.sum_mul, Finset.mul_sum]
      calc ∑ j : Fin D, ∑ k : Fin D, ∑ l : Fin D,
            (inner ℝ (b k) (b_psi j) * phiS k ω₁) * (inner ℝ (b l) (b_psi j) * phiS l ω₁)
          = ∑ k : Fin D, ∑ l : Fin D, (phiS k ω₁ * phiS l ω₁) *
              ∑ j : Fin D, inner ℝ (b k) (b_psi j) * inner ℝ (b l) (b_psi j) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => by ring
        _ = ∑ k : Fin D, ∑ l : Fin D, (phiS k ω₁ * phiS l ω₁) * inner ℝ (b k) (b l) := by
            refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
            congr 1
            have hrep_l : ∑ j : Fin D, inner ℝ (b_psi j) (b l) • b_psi j = b l := by
              simpa [b_psi.repr_apply_apply] using b_psi.sum_repr (b l)
            have h1 : inner ℝ (b k) (b l) =
                ∑ j : Fin D, inner ℝ (b k) (b_psi j) * inner ℝ (b l) (b_psi j) := by
              conv_lhs => rw [← hrep_l]
              rw [inner_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              exact (inner_smul_right (b k) (b_psi j) (inner ℝ (b_psi j) (b l))).trans (by
                rw [real_inner_comm (b_psi j) (b l), mul_comm])
            exact h1.symm
        _ = ∑ k : Fin D, phiS k ω₁ * phiS k ω₁ := by
            refine Finset.sum_congr rfl fun k hk => ?_
            have hbo : ∀ l, inner ℝ (b k) (b l) = if k = l then 1 else 0 :=
              orthonormal_iff_ite.mp b.orthonormal k
            simp_rw [hbo]
            rw [Finset.sum_eq_single k]
            · simp
            · intro l _ hlk; simp [Ne.symm hlk]
            · intro hnot; exact absurd hk hnot
    intro ω₀
    have hconst_ω : (fun ω => ∑ j : Fin D, (phiS j ω) ^ 2) = fun _ => ∑ j : Fin D, (phiS j ω₀) ^ 2 := by
      ext ω; exact hconst ω ω₀
    have hint1 : ∫ ω, ∑ j : Fin D, (phiS j ω) ^ 2 ∂(μS n) = ∑ j : Fin D, (phiS j ω₀) ^ 2 := by
      rw [hconst_ω, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    have hint2 : ∫ ω, ∑ j : Fin D, (phiS j ω) ^ 2 ∂(μS n) = (D : ℝ) := by
      have hi : ∀ j : Fin D, Integrable (fun ω => (phiS j ω) ^ 2) (μS n) :=
        fun j => (memLp_of_mem_V_d hn1 d (phiV j).2).integrable_sq
      rw [integral_finsetSum _ fun j _ => hi j]
      have hsq1 : ∀ j : Fin D, ∫ ω, (phiS j ω) ^ 2 ∂(μS n) = 1 := by
        intro j
        simpa [sq] using hphi_ortho j j
      simp [hsq1]
    linarith
  exact ⟨D, phiS, rfl, fun i => (phiV i).2, hphi_ortho, hphi_span, hsum_sq⟩

/-! ### Positive-Operator Cauchy-Schwarz & `H`-Valued Concentration Inequality -/

private lemma rclike_re_eq (z : ℂ) : RCLike.re z = z.re := rfl

private lemma complex_sum_re {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

lemma re_inner_pos_op_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {E_op : H →L[ℂ] H} (hE : E_op.IsPositive) (x y : H) :
    (RCLike.re (inner ℂ x (E_op y))) ^ 2 ≤
      RCLike.re (inner ℂ x (E_op x)) * RCLike.re (inner ℂ y (E_op y)) := by
  let a : ℝ := RCLike.re (inner ℂ x (E_op x))
  let b : ℝ := RCLike.re (inner ℂ x (E_op y))
  let c : ℝ := RCLike.re (inner ℂ y (E_op y))
  have ha : 0 ≤ a := hE.re_inner_nonneg_right x
  have hc : 0 ≤ c := hE.re_inner_nonneg_right y
  have hquad : ∀ r : ℝ, 0 ≤ a + 2 * b * r + c * r ^ 2 := by
    intro r
    have hnn := hE.re_inner_nonneg_right (x + (r : ℂ) • y)
    have hexp : RCLike.re (inner ℂ (x + (r : ℂ) • y) (E_op (x + (r : ℂ) • y))) =
        a + 2 * b * r + c * r ^ 2 := by
      rw [map_add, map_smul, inner_add_left, inner_add_right, inner_add_right,
        inner_smul_left, inner_smul_right, inner_smul_right, inner_smul_left]
      simp_rw [rclike_re_eq]
      simp only [Complex.add_re, Complex.conj_ofReal, Complex.re_ofReal_mul]
      have hsym : (inner ℂ y (E_op x)).re = b := by
        have h1 : inner ℂ (E_op y) x = inner ℂ y (E_op x) := hE.isSymmetric y x
        rw [← h1]
        exact inner_re_symm (𝕜 := ℂ) (E_op y) x
      rw [hsym]
      change a + r * b + (r * b + r * (r * c)) = a + 2 * b * r + c * r ^ 2
      ring
    rwa [hexp] at hnn
  rcases eq_or_lt_of_le hc with hc0 | hc_pos
  · rw [← hc0] at hquad
    have hcf : c = 0 := hc0.symm
    change b ^ 2 ≤ a * c
    rw [hcf, mul_zero]
    by_cases hb : b = 0
    · simp [hb]
    · exfalso
      have hneg := hquad (-(a + 1) / (2 * b))
      have hval : a + 2 * b * (-(a + 1) / (2 * b)) + 0 * (-(a + 1) / (2 * b)) ^ 2 = -1 := by
        field_simp [hb]
        ring
      linarith
  · have hmin := hquad (-b / c)
    have hval : a + 2 * b * (-b / c) + c * (-b / c) ^ 2 = (a * c - b ^ 2) / c := by
      field_simp [hc_pos.ne']
      ring
    rw [hval, le_div_iff₀ hc_pos, zero_mul] at hmin
    change b ^ 2 ≤ a * c
    linarith

lemma re_inner_pos_op_sum_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {E_op : H →L[ℂ] H} (hE : E_op.IsPositive) (D : ℕ) (a : Fin D → ℝ) (v : Fin D → H) :
    RCLike.re (inner ℂ (∑ i : Fin D, (a i : ℂ) • v i)
        (E_op (∑ j : Fin D, (a j : ℂ) • v j))) ≤
      (∑ i : Fin D, (a i) ^ 2) * ∑ i : Fin D, RCLike.re (inner ℂ (v i) (E_op (v i))) := by
  let q : Fin D → ℝ := fun i => RCLike.re (inner ℂ (v i) (E_op (v i)))
  have hq_nn : ∀ i, 0 ≤ q i := fun i => hE.re_inner_nonneg_right (v i)
  have hexp : RCLike.re (inner ℂ (∑ i : Fin D, (a i : ℂ) • v i)
        (E_op (∑ j : Fin D, (a j : ℂ) • v j))) =
      ∑ i : Fin D, ∑ j : Fin D, (a i * a j) * RCLike.re (inner ℂ (v i) (E_op (v j))) := by
    rw [map_sum, sum_inner]
    simp only [map_sum, map_smul, inner_sum, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal]
    simp only [rclike_re_eq, Complex.re_ofReal_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hexp]
  have hterm : ∀ i j : Fin D,
      (a i * a j) * RCLike.re (inner ℂ (v i) (E_op (v j))) ≤
        (|a i| * Real.sqrt (q i)) * (|a j| * Real.sqrt (q j)) := by
    intro i j
    have hcs := re_inner_pos_op_le hE (v i) (v j)
    have hab : |RCLike.re (inner ℂ (v i) (E_op (v j)))| ≤ Real.sqrt (q i) * Real.sqrt (q j) := by
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (hq_nn i)]
      exact Real.sqrt_le_sqrt hcs
    calc (a i * a j) * RCLike.re (inner ℂ (v i) (E_op (v j)))
        ≤ |a i * a j * RCLike.re (inner ℂ (v i) (E_op (v j)))| := le_abs_self _
      _ = |a i| * |a j| * |RCLike.re (inner ℂ (v i) (E_op (v j)))| := by rw [abs_mul, abs_mul]
      _ ≤ (|a i| * |a j|) * (Real.sqrt (q i) * Real.sqrt (q j)) :=
          mul_le_mul_of_nonneg_left hab (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = (|a i| * Real.sqrt (q i)) * (|a j| * Real.sqrt (q j)) := by ring
  calc ∑ i : Fin D, ∑ j : Fin D, (a i * a j) * RCLike.re (inner ℂ (v i) (E_op (v j)))
      ≤ ∑ i : Fin D, ∑ j : Fin D, (|a i| * Real.sqrt (q i)) * (|a j| * Real.sqrt (q j)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = (∑ i : Fin D, |a i| * Real.sqrt (q i)) ^ 2 := by
        rw [sq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ ≤ (∑ i : Fin D, |a i| ^ 2) * ∑ i : Fin D, (Real.sqrt (q i)) ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |a i|) (fun i => Real.sqrt (q i))
    _ = (∑ i : Fin D, (a i) ^ 2) * ∑ i : Fin D, q i := by
        congr 1
        · refine Finset.sum_congr rfl fun i _ => sq_abs (a i)
        · refine Finset.sum_congr rfl fun i _ => Real.sq_sqrt (hq_nn i)

lemma H_deg_concentration {n : ℕ} (hn : 2 ≤ n) (d : ℕ)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (E_op : H →L[ℂ] H) (hE : E_op.IsPositive) (v : (Fin n → ℕ) → H)
    {A : Set (Metric.sphere (0 : E n) 1)} (hA : MeasurableSet A) :
    let L : E n → H := fun g => ∑ α ∈ I_deg n d, (Hnd α g : ℂ) • v α
    Integrable (fun g : E n => RCLike.re (inner ℂ (L g) (E_op (L g)))) (γ n) ∧
    ∫ g in cone A, RCLike.re (inner ℂ (L g) (E_op (L g))) ∂(γ n) ≤
      (Module.finrank ℝ (V_d n d) : ℝ) * (μS n).real A *
        ∫ g : E n, RCLike.re (inner ℂ (L g) (E_op (L g))) ∂(γ n) := by
  intro L
  have hn1 : 1 ≤ n := by omega
  have : IsProbabilityMeasure (μS n) := isProbabilityMeasure_μS hn1
  have hL_cont : Continuous L := by
    refine continuous_finsetSum _ fun α _ => ?_
    exact (Complex.continuous_ofReal.comp (continuous_Hnd α)).smul continuous_const
  let F : E n → ℝ := fun g => RCLike.re (inner ℂ (L g) (E_op (L g)))
  have hF_cont : Continuous F :=
    Complex.continuous_re.comp (hL_cont.inner (E_op.continuous.comp hL_cont))
  have hF_nn : ∀ g, 0 ≤ F g := fun g => hE.re_inner_nonneg_right (L g)
  have hF_int : Integrable F (γ n) := by
    let C : ℝ := ‖E_op‖ * (I_deg n d).card
    have hdom_int : Integrable (fun g : E n => C * ∑ α ∈ I_deg n d, (Hnd α g) ^ 2 * ‖v α‖ ^ 2) (γ n) :=
      (integrable_finsetSum _ fun α _ =>
        ((integrable_Hnd_mul_Hnd α α).congr (ae_of_all _ fun g => (sq (Hnd α g)).symm)).mul_const
          (‖v α‖ ^ 2)).const_mul C
    refine hdom_int.mono' hF_cont.aestronglyMeasurable (ae_of_all _ fun g => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hF_nn g)]
    have h1 : F g ≤ ‖L g‖ * ‖E_op (L g)‖ := by
      have hre : RCLike.re (inner ℂ (L g) (E_op (L g))) ≤ ‖inner ℂ (L g) (E_op (L g))‖ :=
        Complex.re_le_norm _
      exact hre.trans (norm_inner_le_norm _ _)
    have h2 : ‖L g‖ * ‖E_op (L g)‖ ≤ ‖E_op‖ * ‖L g‖ ^ 2 := by
      have ho : ‖E_op (L g)‖ ≤ ‖E_op‖ * ‖L g‖ := E_op.le_opNorm (L g)
      calc ‖L g‖ * ‖E_op (L g)‖ ≤ ‖L g‖ * (‖E_op‖ * ‖L g‖) :=
            mul_le_mul_of_nonneg_left ho (norm_nonneg _)
        _ = ‖E_op‖ * ‖L g‖ ^ 2 := by ring
    have h3 : ‖L g‖ ^ 2 ≤ (I_deg n d).card * ∑ α ∈ I_deg n d, (Hnd α g) ^ 2 * ‖v α‖ ^ 2 := by
      have hnorm_sum : ‖L g‖ ≤ ∑ α ∈ I_deg n d, 1 * ‖(Hnd α g : ℂ) • v α‖ := by
        dsimp only [L]
        simpa using norm_sum_le (I_deg n d) fun α => (Hnd α g : ℂ) • v α
      have hsq : ‖L g‖ ^ 2 ≤ (∑ α ∈ I_deg n d, (1 : ℝ) * ‖(Hnd α g : ℂ) • v α‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm_sum 2
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (I_deg n d)
        (fun _ : Fin n → ℕ => (1 : ℝ)) (fun α => ‖(Hnd α g : ℂ) • v α‖)
      have hterm_sq : ∀ α, ‖(Hnd α g : ℂ) • v α‖ ^ 2 = (Hnd α g) ^ 2 * ‖v α‖ ^ 2 := by
        intro α
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      simp_rw [hterm_sq] at hcs
      simp only [Finset.sum_const, nsmul_eq_mul, one_pow, mul_one] at hcs
      exact hsq.trans hcs
    calc F g ≤ ‖E_op‖ * ‖L g‖ ^ 2 := h1.trans h2
      _ ≤ ‖E_op‖ * ((I_deg n d).card * ∑ α ∈ I_deg n d, (Hnd α g) ^ 2 * ‖v α‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ = C * ∑ α ∈ I_deg n d, (Hnd α g) ^ 2 * ‖v α‖ ^ 2 := by dsimp [C]; ring
  refine ⟨hF_int, ?_⟩
  obtain ⟨D, phiS, hD, hphiV, hphi_ortho, hphi_span, hsum_sq⟩ := spherical_basis hn d
  have hF_cone_int : Integrable (cone A |>.indicator F) (γ n) :=
    hF_int.indicator (measurableSet_cone hA)
  obtain ⟨hpol_all, hint_rad_all⟩ := integral_gamma_polar hn hF_int
  obtain ⟨hpol_cone, hint_rad_cone⟩ := integral_gamma_polar hn hF_cone_int
  rw [← integral_indicator (measurableSet_cone hA), hpol_cone, hpol_all, ← hD, ← integral_const_mul]
  refine integral_mono_ae hint_rad_cone (hint_rad_all.const_mul _) ?_
  -- Pointwise bound on spheres for each `r > 0`
  have hr_bound : ∀ r : ℝ, 0 < r →
      (∫ ω : Metric.sphere (0 : E n) 1, (cone A).indicator F (r • ω.1) ∂(μS n)) ≤
        (D : ℝ) * (μS n).real A * ∫ ω : Metric.sphere (0 : E n) 1, F (r • ω.1) ∂(μS n) := by
    intro r hr
    let a : (Fin n → ℕ) → Fin D → ℝ := fun α j =>
      ∫ ω' : Metric.sphere (0 : E n) 1, phiS j ω' * Hnd α (r • ω'.1) ∂(μS n)
    have hHnd_exp : ∀ α ∈ I_deg n d, ∀ ω : Metric.sphere (0 : E n) 1,
        Hnd α (r • ω.1) = ∑ j : Fin D, a α j * phiS j ω := by
      intro α hα ω
      have hmem : (fun ω' : Metric.sphere (0 : E n) 1 => Hnd α (r • ω'.1)) ∈ V_d n d :=
        ⟨fun g => Hnd α (r • g), P_Hnd_comp_smul r (Submodule.subset_span ⟨α, hα, rfl⟩), rfl⟩
      exact hphi_span _ hmem ω
    let c : Fin D → H := fun j => ∑ α ∈ I_deg n d, (a α j : ℂ) • v α
    have hL_exp : ∀ ω : Metric.sphere (0 : E n) 1,
        L (r • ω.1) = ∑ j : Fin D, (phiS j ω : ℂ) • c j := by
      intro ω
      dsimp only [L, c]
      have hterm : ∀ α ∈ I_deg n d,
          (Hnd α (r • ω.1) : ℂ) • v α = ∑ j : Fin D, (phiS j ω : ℂ) • ((a α j : ℂ) • v α) := by
        intro α hα
        rw [hHnd_exp α hα ω]
        push_cast
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_smul, mul_comm]
      rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => (Finset.smul_sum).symm
    have hF_pt : ∀ ω : Metric.sphere (0 : E n) 1,
        F (r • ω.1) ≤ (D : ℝ) * ∑ j : Fin D, RCLike.re (inner ℂ (c j) (E_op (c j))) := by
      intro ω
      dsimp only [F]
      rw [hL_exp ω]
      have hcs := re_inner_pos_op_sum_le hE D (fun j => phiS j ω) c
      rwa [hsum_sq ω] at hcs
    have hF_sph_eq : (∫ ω : Metric.sphere (0 : E n) 1, F (r • ω.1) ∂(μS n)) =
        ∑ j : Fin D, RCLike.re (inner ℂ (c j) (E_op (c j))) := by
      have hexp_ω : ∀ ω : Metric.sphere (0 : E n) 1,
          F (r • ω.1) = ∑ i : Fin D, ∑ j : Fin D,
            (phiS i ω * phiS j ω) * RCLike.re (inner ℂ (c i) (E_op (c j))) := by
        intro ω
        dsimp only [F]
        rw [hL_exp ω, map_sum, sum_inner]
        simp only [map_sum, map_smul, inner_sum, inner_smul_left, inner_smul_right,
          Complex.conj_ofReal]
        simp only [rclike_re_eq, Complex.re_ofReal_mul]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      simp_rw [hexp_ω]
      have hi_prod : ∀ i j : Fin D,
          Integrable (fun ω : Metric.sphere (0 : E n) 1 =>
            (phiS i ω * phiS j ω) * RCLike.re (inner ℂ (c i) (E_op (c j)))) (μS n) := by
        intro i j
        have hmem_i : MemLp (phiS i) 2 (μS n) := memLp_of_mem_V_d hn1 d (hphiV i)
        have hmem_j : MemLp (phiS j) 2 (μS n) := memLp_of_mem_V_d hn1 d (hphiV j)
        have hm := ((hmem_i.integrable_sq.add hmem_j.integrable_sq).div_const 2).mono'
          (hmem_i.1.mul hmem_j.1) (ae_of_all _ fun ω => by
            rw [Real.norm_eq_abs]
            dsimp only [Pi.add_apply, Pi.mul_apply]
            nlinarith [abs_nonneg (phiS i ω), abs_nonneg (phiS j ω), abs_mul (phiS i ω) (phiS j ω),
              sq_abs (phiS i ω), sq_abs (phiS j ω), sq_nonneg (|phiS i ω| - |phiS j ω|)])
        exact hm.mul_const _
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi_prod i j]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [integral_finsetSum _ fun j _ => hi_prod i j]
      simp_rw [integral_mul_const, hphi_ortho i]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hij; simp [Ne.symm hij]
      · intro hnot; exact absurd hi hnot
    have hind_eq : (fun ω : Metric.sphere (0 : E n) 1 => (cone A).indicator F (r • ω.1)) =
        A.indicator (fun ω => F (r • ω.1)) := by
      ext ω; exact cone_indicator_radial A F hr ω
    rw [hind_eq]
    have hint_A : Integrable (fun ω : Metric.sphere (0 : E n) 1 => F (r • ω.1)) (μS n) :=
      Integrable.of_bound (hF_cont.comp (continuous_subtype_val.const_smul r)).aestronglyMeasurable
        ((D : ℝ) * ∑ j : Fin D, RCLike.re (inner ℂ (c j) (E_op (c j))))
        (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hF_nn _)]
          exact hF_pt ω)
    have hconst_dom : ∫ ω : Metric.sphere (0 : E n) 1,
          A.indicator (fun ω => F (r • ω.1)) ω ∂(μS n) ≤
        ∫ ω : Metric.sphere (0 : E n) 1,
          A.indicator (fun _ => (D : ℝ) * ∑ j : Fin D, RCLike.re (inner ℂ (c j) (E_op (c j)))) ω ∂(μS n) := by
      refine integral_mono_ae (hint_A.indicator hA) ((integrable_const _).indicator hA)
        (ae_of_all _ fun ω => ?_)
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
        exact hF_pt ω
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
    have hconst_eval : ∫ ω : Metric.sphere (0 : E n) 1,
          A.indicator (fun _ => (D : ℝ) * ∑ j : Fin D, RCLike.re (inner ℂ (c j) (E_op (c j)))) ω ∂(μS n) =
        ((D : ℝ) * ∑ j : Fin D, RCLike.re (inner ℂ (c j) (E_op (c j)))) * (μS n).real A := by
      rw [integral_indicator hA, setIntegral_const, smul_eq_mul, mul_comm]
    rw [hF_sph_eq]
    calc ∫ ω : Metric.sphere (0 : E n) 1, A.indicator (fun ω => F (r • ω.1)) ω ∂(μS n)
        ≤ ((D : ℝ) * ∑ j : Fin D, RCLike.re (inner ℂ (c j) (E_op (c j)))) * (μS n).real A :=
          hconst_dom.trans_eq hconst_eval
      _ = (D : ℝ) * (μS n).real A * ∑ j : Fin D, RCLike.re (inner ℂ (c j) (E_op (c j))) := by
          ring
  -- Multiply by `radialWeight n r` and integrate over `Ioi 0`
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr_pos : 0 < r := hr
  calc radialWeight n r * ∫ ω : Metric.sphere (0 : E n) 1, (cone A).indicator F (r • ω.1) ∂(μS n)
      ≤ radialWeight n r * ((D : ℝ) * (μS n).real A *
          ∫ ω : Metric.sphere (0 : E n) 1, F (r • ω.1) ∂(μS n)) :=
        mul_le_mul_of_nonneg_left (hr_bound r hr_pos) (radialWeight_nonneg hr_pos.le)
    _ = (D : ℝ) * (μS n).real A * (radialWeight n r *
          ∫ ω : Metric.sphere (0 : E n) 1, F (r • ω.1) ∂(μS n)) := by ring


-- Module 4: QMemLearner representation, countable support, null bad hyperplane set,
-- continuity on Zᶜ, inductive W_H <= 4402^t, finite Borel cover, finite POVM atoms,
-- spherical cap inclusion via lemma_2_1, and > (4/5)^2 lower bound.
-- Concatenated inside `namespace AuxTest1D` after `mod3_spherical.lean`.

section LearnerModule

open QuantumLTF.Membership.Supplement

/-! ### Oracle Involutive Splitting & `W_H` Progress Measure -/

section W_H_Section

variable {n : ℕ}

noncomputable def zPerm {Ω : Type} (c : Ω → Bool) :
    ((E n × Bool) × Ω) ≃ ((E n × Bool) × Ω) :=
  Function.Involutive.toPerm
    (fun p => ((p.1.1, xor p.1.2 (c p.2)), p.2))
    (fun ⟨⟨x, b⟩, ω⟩ => by simp)

private lemma lp_norm_sq_eq_tsum {α : Type*} (ψ : lp (fun _ : α => ℂ) 2) :
    ‖ψ‖ ^ 2 = ∑' p, ‖(ψ : _ → ℂ) p‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) ψ
  have hp2 : (2 : ENNReal).toReal = (2 : ℝ) := by norm_num
  simpa [hp2, Real.rpow_two] using h

noncomputable def Z_flip {Ω : Type} (c : Ω → Bool) :
    lp (fun _ : (E n × Bool) × Ω => ℂ) 2 →L[ℂ]
      lp (fun _ : (E n × Bool) × Ω => ℂ) 2 :=
  LinearMap.mkContinuous
    { toFun := fun ψ =>
        ⟨fun p => (ψ : _ → ℂ) (zPerm c p),
          (memℓp_gen_iff (by norm_num)).2 (((zPerm c).summable_iff
            (f := fun p => ‖(ψ : _ → ℂ) p‖ ^ (2 : ENNReal).toReal)).2
            ((memℓp_gen_iff (p := 2) (by norm_num)).1 ψ.2))⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1
    (fun ψ => by
      rw [one_mul]
      refine le_of_eq ?_
      rw [← Real.rpow_left_inj (norm_nonneg _) (norm_nonneg _) (by norm_num : (2 : ℝ) ≠ 0),
        Real.rpow_two, Real.rpow_two, lp_norm_sq_eq_tsum, lp_norm_sq_eq_tsum]
      exact (zPerm c).tsum_eq (fun p => ‖(ψ : _ → ℂ) p‖ ^ 2))

lemma Z_flip_apply {Ω : Type} (c : Ω → Bool)
    (ψ : lp (fun _ : (E n × Bool) × Ω => ℂ) 2) (p : (E n × Bool) × Ω) :
    Z_flip c ψ p = ψ (zPerm c p) := rfl

lemma Z_flip_invol {Ω : Type} (c : Ω → Bool)
    (ψ : lp (fun _ : (E n × Bool) × Ω => ℂ) 2) :
    Z_flip c (Z_flip c ψ) = ψ := by
  ext p
  simp only [Z_flip_apply, zPerm, Function.Involutive.toPerm, Equiv.coe_fn_mk]
  cases p with | mk xb ω => cases xb with | mk x b => simp

noncomputable def projPos {Ω : Type} (c : Ω → Bool) :
    lp (fun _ : (E n × Bool) × Ω => ℂ) 2 →L[ℂ]
      lp (fun _ : (E n × Bool) × Ω => ℂ) 2 :=
  ((1 / 2 : ℂ)) • (ContinuousLinearMap.id ℂ _ + Z_flip c)

noncomputable def projNeg {Ω : Type} (c : Ω → Bool) :
    lp (fun _ : (E n × Bool) × Ω => ℂ) 2 →L[ℂ]
      lp (fun _ : (E n × Bool) × Ω => ℂ) 2 :=
  ((1 / 2 : ℂ)) • (ContinuousLinearMap.id ℂ _ - Z_flip c)

lemma projPos_add_projNeg {Ω : Type} (c : Ω → Bool)
    (ψ : lp (fun _ : (E n × Bool) × Ω => ℂ) 2) :
    projPos c ψ + projNeg c ψ = ψ := by
  ext p
  simp only [projPos, projNeg, lp.coeFn_add, Pi.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, lp.coeFn_smul, lp.coeFn_sub, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul]
  ring

noncomputable def oracleCLM {Ω : Type} (w : E n) (c : Ω → Bool) :
    lp (fun _ : (E n × Bool) × Ω => ℂ) 2 →L[ℂ]
      lp (fun _ : (E n × Bool) × Ω => ℂ) 2 :=
  LinearMap.mkContinuous
    { toFun := QMemLearner.oracle w c
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1
    (fun ψ => by
      rw [one_mul]
      refine le_of_eq ?_
      rw [← Real.rpow_left_inj (norm_nonneg _) (norm_nonneg _) (by norm_num : (2 : ℝ) ≠ 0),
        Real.rpow_two, Real.rpow_two, lp_norm_sq_eq_tsum, lp_norm_sq_eq_tsum]
      exact (QMemLearner.oraclePerm w c).tsum_eq (fun p => ‖(ψ : _ → ℂ) p‖ ^ 2))

lemma oracle_norm {Ω : Type} (w : E n) (c : Ω → Bool)
    (ψ : lp (fun _ : (E n × Bool) × Ω => ℂ) 2) :
    ‖QMemLearner.oracle w c ψ‖ = ‖ψ‖ := by
  rw [← Real.rpow_left_inj (norm_nonneg _) (norm_nonneg _) (by norm_num : (2 : ℝ) ≠ 0),
    Real.rpow_two, Real.rpow_two, lp_norm_sq_eq_tsum, lp_norm_sq_eq_tsum]
  exact (QMemLearner.oraclePerm w c).tsum_eq (fun p => ‖(ψ : _ → ℂ) p‖ ^ 2)

lemma oracle_projPos {Ω : Type} (w : E n) (c : Ω → Bool)
    (ψ : lp (fun _ : (E n × Bool) × Ω => ℂ) 2) :
    QMemLearner.oracle w c (projPos c ψ) = projPos c ψ := by
  ext ⟨⟨x, b⟩, ω⟩
  simp only [QMemLearner.oracle, QMemLearner.oraclePerm, Function.Involutive.toPerm, Equiv.coe_fn_mk,
    projPos, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply, Z_flip_apply, zPerm, lp.coeFn_smul, lp.coeFn_add,
    Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  cases hc : c ω <;> cases hltf : decide (ltf w 0 x = -1) <;> simp [add_comm]

lemma oracle_projNeg {Ω : Type} (w : E n) (c : Ω → Bool)
    (ψ : lp (fun _ : (E n × Bool) × Ω => ℂ) 2) (p : (E n × Bool) × Ω) :
    QMemLearner.oracle w c (projNeg c ψ) p =
      (sgn (inner ℝ p.1.1 w) : ℂ) * (projNeg c ψ) p := by
  rcases p with ⟨⟨x, b⟩, ω⟩
  simp only [QMemLearner.oracle, QMemLearner.oraclePerm, Function.Involutive.toPerm, Equiv.coe_fn_mk,
    projNeg, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, Z_flip_apply, zPerm, lp.coeFn_smul, lp.coeFn_sub,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul, ltf, sub_zero, sgn]
  have hin : inner ℝ w x = inner ℝ x w := real_inner_comm x w
  rw [hin]
  split_ifs with hinner <;> cases hc : c ω <;> simp <;> ring

noncomputable def W_H {Ω : Type}
    (F : E n → lp (fun _ : (E n × Bool) × Ω => ℂ) 2) : ℝ≥0∞ :=
  ∑' p : (E n × Bool) × Ω,
    (W_real (fun g => (F g p).re) + W_real (fun g => (F g p).im))

lemma coeff_nd_add {f₁ f₂ : E n → ℝ} (h₁ : MemLp f₁ 2 (γ n)) (h₂ : MemLp f₂ 2 (γ n))
    (α : Fin n → ℕ) :
    coeff_nd (fun g => f₁ g + f₂ g) α = coeff_nd f₁ α + coeff_nd f₂ α := by
  unfold coeff_nd
  have hi1 := integrable_mul_of_memLp_two (memLp_Hnd α) h₁
  have hi2 := integrable_mul_of_memLp_two (memLp_Hnd α) h₂
  have heq : (fun g => Hnd α g * (f₁ g + f₂ g)) =
      fun g => Hnd α g * f₁ g + Hnd α g * f₂ g := by ext g; ring
  rw [heq, integral_add hi1 hi2]

lemma coeff_nd_sub {f₁ f₂ : E n → ℝ} (h₁ : MemLp f₁ 2 (γ n)) (h₂ : MemLp f₂ 2 (γ n))
    (α : Fin n → ℕ) :
    coeff_nd (fun g => f₁ g - f₂ g) α = coeff_nd f₁ α - coeff_nd f₂ α := by
  unfold coeff_nd
  have hi1 := integrable_mul_of_memLp_two (memLp_Hnd α) h₁
  have hi2 := integrable_mul_of_memLp_two (memLp_Hnd α) h₂
  have heq : (fun g => Hnd α g * (f₁ g - f₂ g)) =
      fun g => Hnd α g * f₁ g - Hnd α g * f₂ g := by ext g; ring
  rw [heq, integral_sub hi1 hi2]

lemma coeff_nd_const_mul (c : ℝ) {f : E n → ℝ} (α : Fin n → ℕ) :
    coeff_nd (fun g => c * f g) α = c * coeff_nd f α := by
  unfold coeff_nd
  have heq : (fun g => Hnd α g * (c * f g)) = fun g => c * (Hnd α g * f g) := by ext g; ring
  rw [heq, integral_const_mul]

lemma W_H_projPos_add_projNeg {Ω : Type} (c : Ω → Bool)
    (F : E n → lp (fun _ : (E n × Bool) × Ω => ℂ) 2)
    (hF_mem : ∀ p, MemLp (fun g => (F g p).re) 2 (γ n) ∧
      MemLp (fun g => (F g p).im) 2 (γ n)) :
    W_H (fun g => projPos c (F g)) + W_H (fun g => projNeg c (F g)) = W_H F := by
  let flipP : ((E n × Bool) × Ω) → ((E n × Bool) × Ω) := zPerm c
  have hmem_flip : ∀ p, MemLp (fun g => (F g (flipP p)).re) 2 (γ n) ∧
      MemLp (fun g => (F g (flipP p)).im) 2 (γ n) := fun p => hF_mem (flipP p)
  have hpair : ∀ (u v : E n → ℝ) (hu : MemLp u 2 (γ n)) (hv : MemLp v 2 (γ n)),
      W_real (fun g => (1 / 2 : ℝ) * (u g + v g)) +
        W_real (fun g => (1 / 2 : ℝ) * (u g - v g)) =
      (1 / 2 : ℝ≥0∞) * (W_real u + W_real v) := by
    intro u v hu hv
    unfold W_real
    rw [← ENNReal.tsum_add, ← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun α => ?_
    have hc1 : coeff_nd (fun g => (1 / 2 : ℝ) * (u g + v g)) α =
        (1 / 2 : ℝ) * (coeff_nd u α + coeff_nd v α) := by
      rw [coeff_nd_const_mul, coeff_nd_add hu hv]
    have hc2 : coeff_nd (fun g => (1 / 2 : ℝ) * (u g - v g)) α =
        (1 / 2 : ℝ) * (coeff_nd u α - coeff_nd v α) := by
      rw [coeff_nd_const_mul, coeff_nd_sub hu hv]
    rw [hc1, hc2]
    set w : ℝ := (1 + (totalDeg α : ℝ)) ^ (1 / 4 : ℝ)
    have hw : 0 ≤ w := by positivity
    have halg : w * ((1 / 2 : ℝ) * (coeff_nd u α + coeff_nd v α)) ^ 2 +
          w * ((1 / 2 : ℝ) * (coeff_nd u α - coeff_nd v α)) ^ 2 =
        (1 / 2 : ℝ) * (w * (coeff_nd u α) ^ 2 + w * (coeff_nd v α) ^ 2) := by ring
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), halg,
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  have hterm : ∀ p : (E n × Bool) × Ω,
      (W_real (fun g => (projPos c (F g) p).re) + W_real (fun g => (projPos c (F g) p).im)) +
        (W_real (fun g => (projNeg c (F g) p).re) + W_real (fun g => (projNeg c (F g) p).im)) =
      (1 / 2 : ℝ≥0∞) *
        ((W_real (fun g => (F g p).re) + W_real (fun g => (F g p).im)) +
         (W_real (fun g => (F g (flipP p)).re) + W_real (fun g => (F g (flipP p)).im))) := by
    intro p
    have hre_pos : (fun g => (projPos c (F g) p).re) =
        fun g => (1 / 2 : ℝ) * ((F g p).re + (F g (flipP p)).re) := by
      ext g
      simp only [projPos, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.id_apply, Z_flip_apply, lp.coeFn_smul, lp.coeFn_add,
        Pi.smul_apply, Pi.add_apply, smul_eq_mul, flipP]
      simp [Complex.mul_re, Complex.add_re]
    have him_pos : (fun g => (projPos c (F g) p).im) =
        fun g => (1 / 2 : ℝ) * ((F g p).im + (F g (flipP p)).im) := by
      ext g
      simp only [projPos, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.id_apply, Z_flip_apply, lp.coeFn_smul, lp.coeFn_add,
        Pi.smul_apply, Pi.add_apply, smul_eq_mul, flipP]
      simp [Complex.mul_im, Complex.add_im]
    have hre_neg : (fun g => (projNeg c (F g) p).re) =
        fun g => (1 / 2 : ℝ) * ((F g p).re - (F g (flipP p)).re) := by
      ext g
      simp only [projNeg, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.id_apply, Z_flip_apply, lp.coeFn_smul, lp.coeFn_sub,
        Pi.smul_apply, Pi.sub_apply, smul_eq_mul, flipP]
      simp [Complex.mul_re, Complex.sub_re]
    have him_neg : (fun g => (projNeg c (F g) p).im) =
        fun g => (1 / 2 : ℝ) * ((F g p).im - (F g (flipP p)).im) := by
      ext g
      simp only [projNeg, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.id_apply, Z_flip_apply, lp.coeFn_smul, lp.coeFn_sub,
        Pi.smul_apply, Pi.sub_apply, smul_eq_mul, flipP]
      simp [Complex.mul_im, Complex.sub_im]
    rw [hre_pos, him_pos, hre_neg, him_neg]
    have hp_re := hpair _ _ (hF_mem p).1 (hmem_flip p).1
    have hp_im := hpair _ _ (hF_mem p).2 (hmem_flip p).2
    calc (W_real (fun g => (1 / 2 : ℝ) * ((F g p).re + (F g (flipP p)).re)) +
            W_real (fun g => (1 / 2 : ℝ) * ((F g p).im + (F g (flipP p)).im))) +
          (W_real (fun g => (1 / 2 : ℝ) * ((F g p).re - (F g (flipP p)).re)) +
            W_real (fun g => (1 / 2 : ℝ) * ((F g p).im - (F g (flipP p)).im)))
        = (W_real (fun g => (1 / 2 : ℝ) * ((F g p).re + (F g (flipP p)).re)) +
            W_real (fun g => (1 / 2 : ℝ) * ((F g p).re - (F g (flipP p)).re))) +
          (W_real (fun g => (1 / 2 : ℝ) * ((F g p).im + (F g (flipP p)).im)) +
            W_real (fun g => (1 / 2 : ℝ) * ((F g p).im - (F g (flipP p)).im))) := by abel
      _ = (1 / 2 : ℝ≥0∞) * (W_real (fun g => (F g p).re) + W_real (fun g => (F g (flipP p)).re)) +
          (1 / 2 : ℝ≥0∞) * (W_real (fun g => (F g p).im) + W_real (fun g => (F g (flipP p)).im)) := by
          rw [hp_re, hp_im]
      _ = (1 / 2 : ℝ≥0∞) *
            ((W_real (fun g => (F g p).re) + W_real (fun g => (F g p).im)) +
             (W_real (fun g => (F g (flipP p)).re) + W_real (fun g => (F g (flipP p)).im))) := by
          rw [← mul_add]; congr 1; abel
  unfold W_H
  rw [← ENNReal.tsum_add]
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
  have hflip_sum : ∑' p : (E n × Bool) × Ω,
        (W_real (fun g => (F g (flipP p)).re) + W_real (fun g => (F g (flipP p)).im)) =
      ∑' p : (E n × Bool) × Ω,
        (W_real (fun g => (F g p).re) + W_real (fun g => (F g p).im)) :=
    (zPerm c).tsum_eq (fun p => W_real (fun g => (F g p).re) + W_real (fun g => (F g p).im))
  rw [hflip_sum, ← two_mul, ← mul_assoc]
  have h2inv : (1 / 2 : ℝ≥0∞) * 2 = 1 := by
    rw [one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
  rw [h2inv, one_mul]

lemma W_H_oracle_le {Ω : Type} (c : Ω → Bool)
    (F : E n → lp (fun _ : (E n × Bool) × Ω => ℂ) 2)
    (hF_mem : ∀ p, MemLp (fun g => (F g p).re) 2 (γ n) ∧
      MemLp (fun g => (F g p).im) 2 (γ n)) :
    W_H (fun g => QMemLearner.oracle (‖g‖⁻¹ • g) c (F g)) ≤ 4402 * W_H F := by
  let F_pos : E n → lp (fun _ : (E n × Bool) × Ω => ℂ) 2 := fun g => projPos c (F g)
  let F_neg : E n → lp (fun _ : (E n × Bool) × Ω => ℂ) 2 := fun g => projNeg c (F g)
  let G_neg : E n → lp (fun _ : (E n × Bool) × Ω => ℂ) 2 :=
    fun g => QMemLearner.oracle (‖g‖⁻¹ • g) c (F_neg g)
  have hsplit : (fun g => QMemLearner.oracle (‖g‖⁻¹ • g) c (F g)) =
      fun g => F_pos g + G_neg g := by
    ext g p
    have h1 : F g = F_pos g + F_neg g := (projPos_add_projNeg c (F g)).symm
    have h2 : QMemLearner.oracle (‖g‖⁻¹ • g) c (F_pos g + F_neg g) =
        QMemLearner.oracle (‖g‖⁻¹ • g) c (F_pos g) +
          QMemLearner.oracle (‖g‖⁻¹ • g) c (F_neg g) :=
      (oracleCLM (‖g‖⁻¹ • g) c).map_add _ _
    rw [h1, h2, oracle_projPos]
  have hF_neg_mem : ∀ p, MemLp (fun g => (F_neg g p).re) 2 (γ n) ∧
      MemLp (fun g => (F_neg g p).im) 2 (γ n) := by
    intro p
    have hre : (fun g => (F_neg g p).re) =
        fun g => (1 / 2 : ℝ) * ((F g p).re - (F g (zPerm c p)).re) := by
      ext g
      simp only [F_neg, projNeg, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.id_apply, Z_flip_apply, lp.coeFn_smul, lp.coeFn_sub,
        Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      simp [Complex.mul_re, Complex.sub_re]
    have him : (fun g => (F_neg g p).im) =
        fun g => (1 / 2 : ℝ) * ((F g p).im - (F g (zPerm c p)).im) := by
      ext g
      simp only [F_neg, projNeg, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.id_apply, Z_flip_apply, lp.coeFn_smul, lp.coeFn_sub,
        Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      simp [Complex.mul_im, Complex.sub_im]
    rw [hre, him]
    exact ⟨((hF_mem p).1.sub (hF_mem (zPerm c p)).1).const_mul _,
      ((hF_mem p).2.sub (hF_mem (zPerm c p)).2).const_mul _⟩
  have hF_pos_mem : ∀ p, MemLp (fun g => (F_pos g p).re) 2 (γ n) ∧
      MemLp (fun g => (F_pos g p).im) 2 (γ n) := by
    intro p
    have hre : (fun g => (F_pos g p).re) =
        fun g => (1 / 2 : ℝ) * ((F g p).re + (F g (zPerm c p)).re) := by
      ext g
      simp only [F_pos, projPos, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.id_apply, Z_flip_apply, lp.coeFn_smul, lp.coeFn_add,
        Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      simp [Complex.mul_re, Complex.add_re]
    have him : (fun g => (F_pos g p).im) =
        fun g => (1 / 2 : ℝ) * ((F g p).im + (F g (zPerm c p)).im) := by
      ext g
      simp only [F_pos, projPos, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.id_apply, Z_flip_apply, lp.coeFn_smul, lp.coeFn_add,
        Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      simp [Complex.mul_im, Complex.add_im]
    rw [hre, him]
    exact ⟨((hF_mem p).1.add (hF_mem (zPerm c p)).1).const_mul _,
      ((hF_mem p).2.add (hF_mem (zPerm c p)).2).const_mul _⟩
  have hG_neg_mem : ∀ p, MemLp (fun g => (G_neg g p).re) 2 (γ n) ∧
      MemLp (fun g => (G_neg g p).im) 2 (γ n) := by
    intro p
    have hsgn_meas : Measurable (fun g : E n => (sgn (inner ℝ p.1.1 (‖g‖⁻¹ • g)) : ℝ)) := by
      refine (measurable_from_top.comp
        (Measurable.ite measurableSet_Ici measurable_const measurable_const)).comp ?_
      exact measurable_const.inner ((continuous_norm.measurable.inv).smul measurable_id)
    have hre : (fun g => (G_neg g p).re) =
        fun g => (sgn (inner ℝ p.1.1 (‖g‖⁻¹ • g)) : ℝ) * (F_neg g p).re := by
      ext g; dsimp only [G_neg, F_neg]; rw [oracle_projNeg]; simp [Complex.mul_re]
    have him : (fun g => (G_neg g p).im) =
        fun g => (sgn (inner ℝ p.1.1 (‖g‖⁻¹ • g)) : ℝ) * (F_neg g p).im := by
      ext g; dsimp only [G_neg, F_neg]; rw [oracle_projNeg]; simp [Complex.mul_im]
    rw [hre, him]
    have h1 := (hF_neg_mem p).1
    have h2 := (hF_neg_mem p).2
    refine ⟨h1.of_le_mul (c := 1) (hsgn_meas.aestronglyMeasurable.mul h1.1) (ae_of_all _ fun g => ?_),
      h2.of_le_mul (c := 1) (hsgn_meas.aestronglyMeasurable.mul h2.1) (ae_of_all _ fun g => ?_)⟩
    · have habs : |(sgn (inner ℝ p.1.1 (‖g‖⁻¹ • g)) : ℝ)| = 1 := by
        simp only [sgn]; split_ifs <;> norm_num
      rw [one_mul, Real.norm_eq_abs, abs_mul, habs, one_mul, Real.norm_eq_abs]
    · have habs : |(sgn (inner ℝ p.1.1 (‖g‖⁻¹ • g)) : ℝ)| = 1 := by
        simp only [sgn]; split_ifs <;> norm_num
      rw [one_mul, Real.norm_eq_abs, abs_mul, habs, one_mul, Real.norm_eq_abs]
  have hG_anti : ∀ g p, G_neg g (zPerm c p) = - G_neg g p := by
    intro g ⟨⟨x, b⟩, ω⟩
    dsimp only [G_neg, F_neg]
    rw [oracle_projNeg, oracle_projNeg]
    simp only [zPerm, Function.Involutive.toPerm, Equiv.coe_fn_mk]
    have hneg : projNeg c (F g) ((x, xor b (c ω)), ω) = - projNeg c (F g) ((x, b), ω) := by
      simp only [projNeg, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.id_apply, Z_flip_apply, zPerm, Function.Involutive.toPerm,
        Equiv.coe_fn_mk, lp.coeFn_smul, lp.coeFn_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      cases hc : c ω <;> simp [hc] <;> ring
    rw [hneg]; ring
  have hF_pos_symm : ∀ g p, F_pos g (zPerm c p) = F_pos g p := by
    intro g ⟨⟨x, b⟩, ω⟩
    simp only [F_pos, projPos, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.id_apply, Z_flip_apply, zPerm, Function.Involutive.toPerm,
      Equiv.coe_fn_mk, lp.coeFn_smul, lp.coeFn_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    cases hc : c ω <;> simp [hc, add_comm]
  -- For any `a, b` with `a(zPerm p) = a(p)` and `b(zPerm p) = -b(p)`, summing `p` and `zPerm p` cancels cross terms `2 a b`!
  have hW_orth_sum : W_H (fun g => F_pos g + G_neg g) = W_H F_pos + W_H G_neg := by
    have hscalar : ∀ (u v : ((E n × Bool) × Ω) → E n → ℝ),
        (∀ p, MemLp (u p) 2 (γ n) ∧ MemLp (v p) 2 (γ n)) →
        (∀ p g, u (zPerm c p) g = u p g) →
        (∀ p g, v (zPerm c p) g = - v p g) →
        ∑' p, W_real (fun g => u p g + v p g) = (∑' p, W_real (u p)) + ∑' p, W_real (v p) := by
      intro u v huv hu_sym hv_anti
      have heq_twice : ∀ f : ((E n × Bool) × Ω) → ℝ≥0∞,
          (2 : ℝ≥0∞) * ∑' p, f p = ∑' p, (f p + f (zPerm c p)) := by
        intro f
        rw [two_mul, ENNReal.tsum_add]
        congr 1
        exact ((zPerm c).tsum_eq f).symm
      have h2eq : (2 : ℝ≥0∞) * ∑' p, W_real (fun g => u p g + v p g) =
          (2 : ℝ≥0∞) * ((∑' p, W_real (u p)) + ∑' p, W_real (v p)) := by
        rw [heq_twice, mul_add, heq_twice, heq_twice, ← ENNReal.tsum_add]
        refine tsum_congr fun p => ?_
        have hsym_eq : W_real (u (zPerm c p)) = W_real (u p) := by
          congr 1; ext g; exact hu_sym p g
        have hanti_eq : W_real (v (zPerm c p)) = W_real (v p) := by
          unfold W_real
          refine tsum_congr fun α => ?_
          congr 2
          have hc : coeff_nd (v (zPerm c p)) α = - coeff_nd (v p) α := by
            unfold coeff_nd
            have heq : (fun g => Hnd α g * v (zPerm c p) g) = fun g => -(Hnd α g * v p g) := by
              ext g; rw [hv_anti p g]; ring
            rw [heq, integral_neg]
          rw [hc, neg_sq]
        have hadd_eq : W_real (fun g => u p g + v p g) + W_real (fun g => u (zPerm c p) g + v (zPerm c p) g) =
            2 * (W_real (u p) + W_real (v p)) := by
          unfold W_real
          rw [← ENNReal.tsum_add, ← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
          refine tsum_congr fun α => ?_
          have h1 : coeff_nd (fun g => u p g + v p g) α = coeff_nd (u p) α + coeff_nd (v p) α :=
            coeff_nd_add (huv p).1 (huv p).2 α
          have h2 : coeff_nd (fun g => u (zPerm c p) g + v (zPerm c p) g) α =
              coeff_nd (u p) α - coeff_nd (v p) α := by
            have heq : (fun g => u (zPerm c p) g + v (zPerm c p) g) = fun g => u p g - v p g := by
              ext g; rw [hu_sym p g, hv_anti p g]; ring
            rw [heq, coeff_nd_sub (huv p).1 (huv p).2 α]
          rw [h1, h2]
          set w : ℝ := (1 + (totalDeg α : ℝ)) ^ (1 / 4 : ℝ)
          have hw : 0 ≤ w := by positivity
          have halg : w * (coeff_nd (u p) α + coeff_nd (v p) α) ^ 2 +
                w * (coeff_nd (u p) α - coeff_nd (v p) α) ^ 2 =
              2 * (w * (coeff_nd (u p) α) ^ 2 + w * (coeff_nd (v p) α) ^ 2) := by ring
          rw [← ENNReal.ofReal_add (by positivity) (by positivity), halg,
            ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_ofNat]
        rw [hadd_eq, hsym_eq, hanti_eq, two_mul]
        ring
      have hhalf : (1 / 2 : ℝ≥0∞) * 2 = 1 := by
        rw [one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
      calc (∑' p, W_real (fun g => u p g + v p g))
          = ((1 / 2 : ℝ≥0∞) * 2) * ∑' p, W_real (fun g => u p g + v p g) := by
            rw [hhalf, one_mul]
        _ = (1 / 2 : ℝ≥0∞) * ((2 : ℝ≥0∞) * ∑' p, W_real (fun g => u p g + v p g)) := by
            rw [mul_assoc]
        _ = (1 / 2 : ℝ≥0∞) * ((2 : ℝ≥0∞) * ((∑' p, W_real (u p)) + ∑' p, W_real (v p))) := by
            rw [h2eq]
        _ = ((1 / 2 : ℝ≥0∞) * 2) * ((∑' p, W_real (u p)) + ∑' p, W_real (v p)) := by
            rw [← mul_assoc]
        _ = (∑' p, W_real (u p)) + ∑' p, W_real (v p) := by
            rw [hhalf, one_mul]
    unfold W_H
    have hre := hscalar (fun p g => (F_pos g p).re) (fun p g => (G_neg g p).re)
      (fun p => ⟨(hF_pos_mem p).1, (hG_neg_mem p).1⟩)
      (fun p g => by simp [hF_pos_symm]) (fun p g => by simp [hG_anti])
    have him := hscalar (fun p g => (F_pos g p).im) (fun p g => (G_neg g p).im)
      (fun p => ⟨(hF_pos_mem p).2, (hG_neg_mem p).2⟩)
      (fun p g => by simp [hF_pos_symm]) (fun p g => by simp [hG_anti])
    simp only [lp.coeFn_add, Pi.add_apply, Complex.add_re, Complex.add_im]
    rw [ENNReal.tsum_add, hre, him, ENNReal.tsum_add, ENNReal.tsum_add]
    abel
  have hG_bound : W_H G_neg ≤ 4402 * W_H F_neg := by
    unfold W_H
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun p => ?_
    rw [mul_add]
    by_cases hx : p.1.1 = 0
    · have hre : (fun g => (G_neg g p).re) = fun g => (F_neg g p).re := by
        ext g; dsimp only [G_neg, F_neg]; rw [oracle_projNeg]; simp [hx, sgn]
      have him : (fun g => (G_neg g p).im) = fun g => (F_neg g p).im := by
        ext g; dsimp only [G_neg, F_neg]; rw [oracle_projNeg]; simp [hx, sgn]
      rw [hre, him]
      exact add_le_add (le_mul_of_one_le_left' (by norm_num)) (le_mul_of_one_le_left' (by norm_num))
    · have hsgn_ae : ∀ᵐ g ∂(γ n),
          (sgn (inner ℝ p.1.1 (‖g‖⁻¹ • g)) : ℝ) = (sgn (inner ℝ g p.1.1) : ℝ) := by
        have hn1 : 1 ≤ n := by
          by_contra hlt
          have hn0 : n = 0 := by omega
          subst hn0
          exact hx (Subsingleton.elim _ _)
        haveI : Nontrivial (E n) := nontrivial_E hn1
        have hnull0 : γ n ({0} : Set (E n)) = 0 := by
          rw [γ_eq_volume_withDensity, withDensity_apply _ (measurableSet_singleton _),
            Measure.restrict_singleton, measure_singleton, zero_smul, lintegral_zero_measure]
        filter_upwards [compl_mem_ae_iff.mpr hnull0] with g hg0
        have hg_ne : g ≠ 0 := hg0
        have hpos : 0 < ‖g‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hg_ne)
        have hmul : inner ℝ p.1.1 (‖g‖⁻¹ • g) = ‖g‖⁻¹ * inner ℝ g p.1.1 := by
          rw [real_inner_smul_right, real_inner_comm p.1.1 g]
        simp only [sgn, hmul]
        split_ifs with h1 h2 h2
        · rfl
        · exfalso; exact h2 (nonneg_of_mul_nonneg_right h1 hpos)
        · exfalso; exact h1 (mul_nonneg hpos.le h2)
        · rfl
      have hW_eq_ae : ∀ (u : E n → ℝ), MemLp u 2 (γ n) →
          W_real (fun g => (sgn (inner ℝ p.1.1 (‖g‖⁻¹ • g)) : ℝ) * u g) =
            W_real (fun g => (sgn (inner ℝ g p.1.1) : ℝ) * u g) := by
        intro u _
        unfold W_real
        refine tsum_congr fun α => ?_
        have hint : coeff_nd (fun g => (sgn (inner ℝ p.1.1 (‖g‖⁻¹ • g)) : ℝ) * u g) α =
            coeff_nd (fun g => (sgn (inner ℝ g p.1.1) : ℝ) * u g) α := by
          unfold coeff_nd
          refine integral_congr_ae ?_
          filter_upwards [hsgn_ae] with g hg
          rw [hg]
        rw [hint]
      have hre_fn : (fun g => (G_neg g p).re) =
          fun g => (sgn (inner ℝ p.1.1 (‖g‖⁻¹ • g)) : ℝ) * (F_neg g p).re := by
        ext g; dsimp only [G_neg, F_neg]; rw [oracle_projNeg]; simp [Complex.mul_re]
      have him_fn : (fun g => (G_neg g p).im) =
          fun g => (sgn (inner ℝ p.1.1 (‖g‖⁻¹ • g)) : ℝ) * (F_neg g p).im := by
        ext g; dsimp only [G_neg, F_neg]; rw [oracle_projNeg]; simp [Complex.mul_im]
      rw [hre_fn, him_fn, hW_eq_ae _ (hF_neg_mem p).1, hW_eq_ae _ (hF_neg_mem p).2]
      exact add_le_add (W_real_sgn_inner_mul_le (hF_neg_mem p).1 p.1.1 hx)
        (W_real_sgn_inner_mul_le (hF_neg_mem p).2 p.1.1 hx)
  rw [hsplit, hW_orth_sum]
  calc W_H F_pos + W_H G_neg
      ≤ W_H F_pos + 4402 * W_H F_neg := add_le_add le_rfl hG_bound
    _ ≤ 4402 * W_H F_pos + 4402 * W_H F_neg :=
        add_le_add (le_mul_of_one_le_left' (by norm_num)) le_rfl
    _ = 4402 * (W_H F_pos + W_H F_neg) := by rw [mul_add]
    _ = 4402 * W_H F := by rw [W_H_projPos_add_projNeg c F hF_mem]

lemma W_H_eq_tsum_norm_sq {Ω : Type}
    (F : E n → lp (fun _ : (E n × Bool) × Ω => ℂ) 2)
    (hF_meas : AEStronglyMeasurable F (γ n))
    (hF_norm : ∀ g, ‖F g‖ = 1)
    (hF_mem : ∀ p, MemLp (fun g => (F g p).re) 2 (γ n) ∧
      MemLp (fun g => (F g p).im) 2 (γ n)) :
    let v : (Fin n → ℕ) → lp (fun _ : (E n × Bool) × Ω => ℂ) 2 :=
      fun α => ∫ g : E n, (Hnd α g : ℂ) • F g ∂(γ n)
    W_H F = ∑' α : Fin n → ℕ, ENNReal.ofReal ((1 + (totalDeg α : ℝ)) ^ (1 / 4 : ℝ) * ‖v α‖ ^ 2) := by
  intro v
  have hv_int : ∀ α : Fin n → ℕ,
      Integrable (fun g : E n => (Hnd α g : ℂ) • F g) (γ n) := by
    intro α
    have hsm : AEStronglyMeasurable (fun g : E n => (Hnd α g : ℂ) • F g) (γ n) :=
      (Complex.continuous_ofReal.comp (continuous_Hnd α)).aestronglyMeasurable.smul hF_meas
    refine (memLp_Hnd α).integrable one_le_two |>.abs.mono' hsm (ae_of_all _ fun g => ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, hF_norm g, mul_one]
  have hv_coord : ∀ α p, (v α) p =
      (coeff_nd (fun g => (F g p).re) α : ℂ) +
        (coeff_nd (fun g => (F g p).im) α : ℂ) * Complex.I := by
    intro α p
    let ev := lp.evalCLM ℂ (fun _ : (E n × Bool) × Ω => ℂ) 2 p
    have hev : (v α) p = ∫ g : E n, (Hnd α g : ℂ) * F g p ∂(γ n) := by
      dsimp only [v]
      change ev (∫ g : E n, (Hnd α g : ℂ) • F g ∂(γ n)) = _
      rw [← ev.integral_comp_comm (hv_int α)]
      rfl
    have hint_c : Integrable (fun g : E n => (Hnd α g : ℂ) * F g p) (γ n) :=
      ev.integrable_comp (hv_int α)
    have hre : (∫ g : E n, (Hnd α g : ℂ) * F g p ∂(γ n)).re =
        coeff_nd (fun g => (F g p).re) α := by
      have hcomm := Complex.reCLM.integral_comp_comm hint_c
      change ∫ g : E n, ((Hnd α g : ℂ) * F g p).re ∂(γ n) =
        (∫ g : E n, (Hnd α g : ℂ) * F g p ∂(γ n)).re at hcomm
      rw [← hcomm]
      refine integral_congr_ae (ae_of_all _ fun g => ?_)
      simp [Complex.mul_re]
    have him : (∫ g : E n, (Hnd α g : ℂ) * F g p ∂(γ n)).im =
        coeff_nd (fun g => (F g p).im) α := by
      have hcomm := Complex.imCLM.integral_comp_comm hint_c
      change ∫ g : E n, ((Hnd α g : ℂ) * F g p).im ∂(γ n) =
        (∫ g : E n, (Hnd α g : ℂ) * F g p ∂(γ n)).im at hcomm
      rw [← hcomm]
      refine integral_congr_ae (ae_of_all _ fun g => ?_)
      simp [Complex.mul_im]
    rw [hev, ← Complex.re_add_im (∫ g : E n, (Hnd α g : ℂ) * F g p ∂(γ n)), hre, him]
  have hv_norm_sq : ∀ α, ENNReal.ofReal ((1 + (totalDeg α : ℝ)) ^ (1 / 4 : ℝ) * ‖v α‖ ^ 2) =
      ∑' p : (E n × Bool) × Ω, ENNReal.ofReal ((1 + (totalDeg α : ℝ)) ^ (1 / 4 : ℝ) *
        ((coeff_nd (fun g => (F g p).re) α) ^ 2 + (coeff_nd (fun g => (F g p).im) α) ^ 2)) := by
    intro α
    have hp2 : (2 : ENNReal).toReal = (2 : ℝ) := by norm_num
    have hsum_norm : ‖v α‖ ^ 2 = ∑' p,
        ((coeff_nd (fun g => (F g p).re) α) ^ 2 + (coeff_nd (fun g => (F g p).im) α) ^ 2) := by
      rw [lp_norm_sq_eq_tsum]
      refine tsum_congr fun p => ?_
      rw [hv_coord α p, Complex.sq_norm, Complex.normSq_apply]
      simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, sq]
    have hsm : Summable fun p =>
        (coeff_nd (fun g => (F g p).re) α) ^ 2 + (coeff_nd (fun g => (F g p).im) α) ^ 2 := by
      have h1 := (lp.memℓp (v α)).summable (p := 2) (by norm_num)
      simp only [hp2, Real.rpow_two] at h1
      refine h1.congr fun p => ?_
      rw [hv_coord α p, Complex.sq_norm, Complex.normSq_apply]
      simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, sq]
    have hmul_sum := hsm.mul_left ((1 + (totalDeg α : ℝ)) ^ (1 / 4 : ℝ))
    rw [hsum_norm, ← tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg (fun p => by positivity) hmul_sum]
  simp_rw [hv_norm_sq]
  rw [ENNReal.tsum_comm]
  unfold W_H W_real
  refine tsum_congr fun p => ?_
  rw [← ENNReal.tsum_add]
  refine tsum_congr fun α => ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), mul_add]

lemma W_H_comp_isom {Ω : Type}
    (U : lp (fun _ : (E n × Bool) × Ω => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : (E n × Bool) × Ω => ℂ) 2)
    (F : E n → lp (fun _ : (E n × Bool) × Ω => ℂ) 2)
    (hF_meas : AEStronglyMeasurable F (γ n))
    (hF_norm : ∀ g, ‖F g‖ = 1)
    (hF_mem : ∀ p, MemLp (fun g => (F g p).re) 2 (γ n) ∧
      MemLp (fun g => (F g p).im) 2 (γ n))
    (hUF_mem : ∀ p, MemLp (fun g => (U (F g) p).re) 2 (γ n) ∧
      MemLp (fun g => (U (F g) p).im) 2 (γ n)) :
    W_H (fun g => U (F g)) = W_H F := by
  have hUF_meas : AEStronglyMeasurable (fun g => U (F g)) (γ n) :=
    U.continuous.comp_aestronglyMeasurable hF_meas
  have hUF_norm : ∀ g, ‖U (F g)‖ = 1 := fun g => by rw [U.norm_map, hF_norm g]
  rw [W_H_eq_tsum_norm_sq _ hUF_meas hUF_norm hUF_mem,
    W_H_eq_tsum_norm_sq _ hF_meas hF_norm hF_mem]
  refine tsum_congr fun α => ?_
  have hv_int : Integrable (fun g : E n => (Hnd α g : ℂ) • F g) (γ n) := by
    have hsm : AEStronglyMeasurable (fun g : E n => (Hnd α g : ℂ) • F g) (γ n) :=
      (Complex.continuous_ofReal.comp (continuous_Hnd α)).aestronglyMeasurable.smul hF_meas
    refine (memLp_Hnd α).integrable one_le_two |>.abs.mono' hsm (ae_of_all _ fun g => ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, hF_norm g, mul_one]
  let U_clm : lp (fun _ : (E n × Bool) × Ω => ℂ) 2 →L[ℂ]
      lp (fun _ : (E n × Bool) × Ω => ℂ) 2 :=
    { toLinearMap := U.toLinearMap
      cont := U.continuous }
  have hU_comm : (∫ g : E n, (Hnd α g : ℂ) • U (F g) ∂(γ n)) =
      U (∫ g : E n, (Hnd α g : ℂ) • F g ∂(γ n)) := by
    have heq : (fun g : E n => (Hnd α g : ℂ) • U (F g)) =
        fun g => U_clm ((Hnd α g : ℂ) • F g) := by
      ext g p
      change ((Hnd α g : ℂ) • U (F g)) p = (U ((Hnd α g : ℂ) • F g)) p
      rw [map_smul]
    rw [heq]
    exact U_clm.integral_comp_comm hv_int
  dsimp only
  rw [hU_comm, U.norm_map]

end W_H_Section

/-! ### Support, Null Set `Z`, Continuity, Inductive `W_H`, Cover, POVM Atoms, & Lower Bound -/

section LearnerBound

variable {n : ℕ} (hn : 2 ≤ n) (L : QMemLearner n)

noncomputable def Ψ (t : ℕ) (g : E n) :
    lp (fun _ : (E n × Bool) × L.Ω => ℂ) 2 :=
  L.stateAt (‖g‖⁻¹ • g) t

lemma Ψ_zero (g : E n) : Ψ L 0 g = L.init := rfl

lemma Ψ_succ (t : ℕ) (g : E n) :
    Ψ L (t + 1) g = L.V t (QMemLearner.oracle (‖g‖⁻¹ • g) (L.ctrl t) (Ψ L t g)) := rfl

lemma Ψ_norm (t : ℕ) (g : E n) : ‖Ψ L t g‖ = 1 := by
  have hstate : ∀ w : E n, ∀ s : ℕ, ‖L.stateAt w s‖ = 1 := by
    intro w s
    induction s with
    | zero => exact L.init_norm
    | succ s ih =>
      dsimp [QMemLearner.stateAt]
      rw [(L.V s).norm_map, oracle_norm, ih]
  exact hstate _ t

lemma lp_countable_support {α : Type*} (ψ : lp (fun _ : α => ℂ) 2) :
    (Function.support (ψ : α → ℂ)).Countable := by
  have hs := ((memℓp_gen_iff (p := 2) (by norm_num)).1 ψ.2).countable_support
  refine hs.mono fun a ha => ?_
  rw [Function.mem_support, ne_eq] at ha ⊢
  have hp2 : (2 : ENNReal).toReal = (2 : ℝ) := by norm_num
  rw [hp2, Real.rpow_two, sq_eq_zero_iff, norm_eq_zero]
  exact ha

open Classical in
noncomputable def suppK : ℕ → Set ((E n × Bool) × L.Ω)
  | 0 => Function.support (L.init : _ → ℂ)
  | t + 1 =>
    let Kt' := suppK t ∪ (fun p : (E n × Bool) × L.Ω => ((p.1.1, !p.1.2), p.2)) '' suppK t
    ⋃ p ∈ Kt', Function.support ((L.V t (lp.single (E := fun _ : (E n × Bool) × L.Ω => ℂ) 2 p (1 : ℂ)) : _ → ℂ))

open Classical in
lemma countable_suppK (t : ℕ) : (suppK L t).Countable := by
  induction t with
  | zero => exact lp_countable_support L.init
  | succ t ih =>
    have ih' : (suppK L t ∪ (fun p : (E n × Bool) × L.Ω => ((p.1.1, !p.1.2), p.2)) '' suppK L t).Countable :=
      ih.union (ih.image _)
    exact ih'.biUnion fun p _ => lp_countable_support _

open Classical in
lemma Ψ_eq_zero_of_not_mem_suppK (t : ℕ) (g : E n) (p : (E n × Bool) × L.Ω)
    (hp : p ∉ suppK L t) : Ψ L t g p = 0 := by
  have hstate : ∀ w : E n, ∀ s : ℕ, ∀ p ∉ suppK L s, L.stateAt w s p = 0 := by
    intro w s
    induction s with
    | zero =>
      intro p hp
      dsimp [QMemLearner.stateAt]
      by_contra hne
      exact hp hne
    | succ s ih =>
      intro q hq
      dsimp [QMemLearner.stateAt]
      let psi := QMemLearner.oracle w (L.ctrl s) (L.stateAt w s)
      let Ks' := suppK L s ∪ (fun p : (E n × Bool) × L.Ω => ((p.1.1, !p.1.2), p.2)) '' suppK L s
      have hpsi_supp : ∀ p ∉ Ks', psi p = 0 := by
        intro p hp
        dsimp [psi, QMemLearner.oracle, QMemLearner.oraclePerm]
        have hnot : ((p.1.1, xor p.1.2 (L.ctrl s p.2 && decide (ltf w 0 p.1.1 = -1))), p.2) ∉ suppK L s := by
          intro hmem
          apply hp
          cases hb : L.ctrl s p.2 && decide (ltf w 0 p.1.1 = -1)
          · rw [hb, Bool.xor_false] at hmem; exact Or.inl hmem
          · rw [hb, Bool.xor_true] at hmem
            refine Or.inr ⟨((p.1.1, !p.1.2), p.2), hmem, ?_⟩
            simp
        exact ih _ hnot
      have hhas := lp.hasSum_single (p := 2) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) psi
      have hhasV := hhas.map (L.V s) (L.V s).continuous
      let ev := lp.evalCLM ℂ (fun _ : (E n × Bool) × L.Ω => ℂ) 2 q
      have hhas_q := hhasV.map ev ev.continuous
      have hterm0 : ∀ p, ev (L.V s (lp.single (E := fun _ : (E n × Bool) × L.Ω => ℂ) 2 p (psi p))) = 0 := by
        intro p
        have hsmul : lp.single (E := fun _ : (E n × Bool) × L.Ω => ℂ) 2 p (psi p) =
            psi p • lp.single (E := fun _ : (E n × Bool) × L.Ω => ℂ) 2 p (1 : ℂ) := by
          rw [← lp.single_smul]; simp
        rw [hsmul, map_smul, map_smul]
        by_cases hpK : p ∈ Ks'
        · have hV0 : ev (L.V s (lp.single (E := fun _ : (E n × Bool) × L.Ω => ℂ) 2 p (1 : ℂ))) = 0 := by
            by_contra hne
            exact hq (Set.mem_biUnion hpK hne)
          rw [hV0, smul_zero]
        · have hp0 : psi p = 0 := hpsi_supp p hpK
          rw [hp0, zero_smul]
      have hzero_sum : HasSum (fun _ : (E n × Bool) × L.Ω => (0 : ℂ)) (ev (L.V s psi)) :=
        hhas_q.congr_fun (fun p => (hterm0 p).symm)
      exact (hasSum_zero.unique hzero_sum).symm
  exact hstate _ t p hp


noncomputable def queryX {n : ℕ} (L : QMemLearner n) : Set (E n) :=
  ⋃ t ≤ L.T, (fun p : (E n × Bool) × L.Ω => p.1.1) '' suppK L t

lemma countable_queryX {n : ℕ} (L : QMemLearner n) : (queryX L).Countable :=
  (Set.to_countable {t : ℕ | t ≤ L.T}).biUnion fun t _ => (countable_suppK L t).image _

noncomputable def badZ {n : ℕ} (L : QMemLearner n) : Set (E n) :=
  ({0} : Set (E n)) ∪ ⋃ x ∈ queryX L \ {0}, {g : E n | inner ℝ g x = 0}

lemma measurableSet_badZ {n : ℕ} (L : QMemLearner n) : MeasurableSet (badZ L) := by
  refine (measurableSet_singleton _).union ?_
  refine MeasurableSet.biUnion ((countable_queryX L).mono Set.sdiff_subset) fun x _ => ?_
  exact (isClosed_singleton.preimage (continuous_id.inner continuous_const)).measurableSet

lemma hyperplane_γ_null {n : ℕ} (x : E n) (hx : x ≠ 0) :
    γ n {g : E n | inner ℝ g x = 0} = 0 := by
  have hn0 : n ≠ 0 := fun h0 => hx (by subst h0; exact Subsingleton.elim x 0)
  rcases Nat.exists_eq_succ_of_ne_zero hn0 with ⟨m, rfl⟩
  let u : E (m + 1) := ‖x‖⁻¹ • x
  have hu : ‖u‖ = 1 := norm_smul_inv_norm hx
  have hnorm_ne : ‖x‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr hx)
  have hset_eq : {g : E (m + 1) | inner ℝ g x = 0} = {g : E (m + 1) | inner ℝ g u = 0} := by
    ext g
    simp only [Set.mem_ofPred_eq, u, real_inner_smul_right, mul_eq_zero, hnorm_ne, false_or]
  rw [hset_eq]
  obtain ⟨b, hb0⟩ := exists_orthonormalBasis_zero u hu
  let R : E (m + 1) ≃ₗᵢ[ℝ] E (m + 1) :=
    (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).equiv b (Equiv.refl _)
  have hR0 : R (EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0) = u := by
    dsimp [R]; rw [OrthonormalBasis.equiv_apply_basis, Equiv.refl_apply, hb0]
  have hinner_R : ∀ g : E (m + 1), inner ℝ (R g) u = g 0 := by
    intro g
    rw [← hR0, R.inner_map_eq_flip, R.symm_apply_apply, EuclideanSpace.inner_basisFun_real (Fin (m + 1))]
  let H0 : Set (E (m + 1)) := {g : E (m + 1) | g 0 = 0}
  have hpre_R : R ⁻¹' {g : E (m + 1) | inner ℝ g u = 0} = H0 := by
    ext g; simp [H0, hinner_R]
  have hmeas_u : MeasurableSet {g : E (m + 1) | inner ℝ g u = 0} :=
    (isClosed_singleton.preimage (continuous_id.inner continuous_const)).measurableSet
  have hmp_R := measurePreserving_isom_γ R
  rw [← hmp_R.measure_preimage hmeas_u.nullMeasurableSet, hpre_R]
  have hpre_split : (splitE_nd m) ⁻¹' (({(0 : ℝ)} : Set ℝ) ×ˢ Set.univ) = H0 := by
    ext g; simp [splitE_nd, H0]
  have hmeas_box : MeasurableSet (({(0 : ℝ)} : Set ℝ) ×ˢ (Set.univ : Set (E m))) :=
    (measurableSet_singleton _).prod MeasurableSet.univ
  have hmp_split := measurePreserving_splitE_nd_γ m
  rw [← hpre_split, hmp_split.measure_preimage hmeas_box.nullMeasurableSet, Measure.prod_prod]
  have hnull_real : ProbabilityTheory.gaussianReal 0 1 {(0 : ℝ)} = 0 := by
    rw [gaussianReal_zero_one_eq_withDensity, withDensity_apply _ (measurableSet_singleton _),
      Measure.restrict_singleton, Real.volume_singleton, zero_smul, lintegral_zero_measure]
  rw [hnull_real, zero_mul]

lemma γ_badZ_eq_zero {n : ℕ} (hn : 2 ≤ n) (L : QMemLearner n) : γ n (badZ L) = 0 := by
  have hnull0 : γ n ({0} : Set (E n)) = 0 := by
    let e0 : E n := EuclideanSpace.single ⟨0, by omega⟩ 1
    have he0 : e0 ≠ 0 := by
      intro h
      have := congrArg (fun v : E n => v ⟨0, by omega⟩) h
      simp [e0] at this
    refine measure_mono_null (fun g hg => ?_) (hyperplane_γ_null e0 he0)
    rw [Set.mem_singleton_iff] at hg
    simp [hg]
  have hnull_bi : γ n (⋃ x ∈ queryX L \ {0}, {g : E n | inner ℝ g x = 0}) = 0 := by
    rw [measure_biUnion_null_iff ((countable_queryX L).mono Set.sdiff_subset)]
    intro x hx
    exact hyperplane_γ_null x hx.2
  exact le_antisymm ((measure_union_le _ _).trans (by rw [hnull0, hnull_bi]; simp)) bot_le

open Classical in
lemma oracle_single_eq {n : ℕ} {Ω : Type} (w : E n) (c : Ω → Bool)
    (p : (E n × Bool) × Ω) (a : ℂ) :
    QMemLearner.oracle w c (lp.single (E := fun _ : (E n × Bool) × Ω => ℂ) 2 p a) =
      lp.single (E := fun _ : (E n × Bool) × Ω => ℂ) 2 (QMemLearner.oraclePerm w c p) a := by
  ext q
  change (lp.single (E := fun _ : (E n × Bool) × Ω => ℂ) 2 p a) (QMemLearner.oraclePerm w c q) =
    lp.single (E := fun _ : (E n × Bool) × Ω => ℂ) 2 (QMemLearner.oraclePerm w c p) a q
  rw [lp.single_apply, lp.single_apply]
  have hperm_invol : Function.Involutive (QMemLearner.oraclePerm w c) := fun ⟨⟨x, b⟩, ω⟩ => by
    simp only [QMemLearner.oraclePerm, Function.Involutive.toPerm, Equiv.coe_fn_mk]
    rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  by_cases hq : q = QMemLearner.oraclePerm w c p
  · rw [hq, hperm_invol p, Pi.single_eq_same, Pi.single_eq_same]
  · have hne : QMemLearner.oraclePerm w c q ≠ p := by
      intro heq
      apply hq
      have := congrArg (QMemLearner.oraclePerm w c) heq
      simpa [hperm_invol q] using this
    rw [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hq]

open Classical in
lemma continuousOn_Ψ {n : ℕ} (L : QMemLearner n) :
    ∀ t ≤ L.T, ContinuousOn (Ψ L t) (badZ L)ᶜ := by
  intro t ht
  induction t with
  | zero =>
    have hfn : Ψ L 0 = fun _ => L.init := rfl
    rw [hfn]
    exact continuousOn_const
  | succ t ih =>
    intro g₀ hg₀
    have ht_le : t ≤ L.T := Nat.le_of_succ_le ht
    have hg₀_ne : g₀ ≠ 0 := fun h0 => hg₀ (Or.inl h0)
    rw [Metric.continuousWithinAt_iff]
    intro η hη
    let psi0 := Ψ L t g₀
    have hhas := (lp.hasSum_single (p := 2) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) psi0)
    rw [HasSum, Metric.tendsto_nhds] at hhas
    obtain ⟨S₀, hS₀⟩ := (hhas (η / 4) (by linarith)).exists
    let S : Finset ((E n × Bool) × L.Ω) := S₀.filter (fun p => p ∈ suppK L t)
    let psiS := ∑ p ∈ S, lp.single 2 p (psi0 p)
    have hS_eq : ∑ p ∈ S₀, lp.single 2 p (psi0 p) = psiS := by
      have hsub : S ⊆ S₀ := Finset.filter_subset _ _
      rw [← Finset.sum_sdiff hsub]
      have hzero : ∑ p ∈ S₀ \ S, lp.single 2 p (psi0 p) = 0 := by
        refine Finset.sum_eq_zero fun p hp => ?_
        have hp_not : p ∉ suppK L t := by
          intro hmem
          exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hp).1, hmem⟩)
        rw [Ψ_eq_zero_of_not_mem_suppK L t g₀ p hp_not, lp.single_zero]
      rw [hzero, zero_add]
    have happrox : ‖psi0 - psiS‖ < η / 4 := by
      rw [← dist_eq_norm, dist_comm, ← hS_eq]
      exact hS₀
    have hih := (Metric.continuousWithinAt_iff.mp (ih ht_le g₀ hg₀)) (η / 2) (by linarith)
    rcases hih with ⟨δ₁, hδ₁_pos, hδ₁⟩
    have hsign_nbhd : ∀ S' : Finset ((E n × Bool) × L.Ω), (∀ p ∈ S', p ∈ suppK L t) →
        ∃ δ₂ > 0, ∀ g : E n, dist g g₀ < δ₂ →
          g ≠ 0 ∧ ∀ p ∈ S', ltf (‖g‖⁻¹ • g) 0 p.1.1 = ltf (‖g₀‖⁻¹ • g₀) 0 p.1.1 := by
      intro S' hS'
      induction S' using Finset.induction_on with
      | empty =>
        refine ⟨‖g₀‖ / 2, half_pos (norm_pos_iff.mpr hg₀_ne), fun g hg => ⟨?_, fun _ hp => False.elim (Finset.notMem_empty _ hp)⟩⟩
        intro h0
        rw [h0, dist_zero_left] at hg
        linarith [norm_pos_iff.mpr hg₀_ne]
      | @insert p s hp_not ih_s =>
        obtain ⟨δs, hδs_pos, hδs⟩ := ih_s (fun q hq => hS' q (Finset.mem_insert_of_mem hq))
        by_cases hx0 : p.1.1 = 0
        · refine ⟨δs, hδs_pos, fun g hg => ⟨(hδs g hg).1, fun q hq => ?_⟩⟩
          rcases Finset.mem_insert.mp hq with hqp | hqs
          · rw [hqp]; simp [ltf, hx0]
          · exact (hδs g hg).2 q hqs
        · have hqx : p.1.1 ∈ queryX L \ {0} :=
            ⟨Set.mem_biUnion ht_le ⟨p, hS' p (Finset.mem_insert_self _ _), rfl⟩, hx0⟩
          have hinner_ne : inner ℝ g₀ p.1.1 ≠ 0 := by
            intro heq
            exact hg₀ (Or.inr (Set.mem_biUnion hqx heq))
          have hcont_in : ContinuousAt (fun g : E n => inner ℝ g p.1.1) g₀ :=
            (continuous_id.inner continuous_const).continuousAt
          obtain ⟨δp, hδp_pos, hδp⟩ := Metric.continuousAt_iff.mp hcont_in
            |inner ℝ g₀ p.1.1| (abs_pos.mpr hinner_ne)
          refine ⟨min δs δp, lt_min hδs_pos hδp_pos, fun g hg => ?_⟩
          have hgs := hδs g (lt_of_lt_of_le hg (min_le_left _ _))
          refine ⟨hgs.1, fun q hq => ?_⟩
          rcases Finset.mem_insert.mp hq with hqp | hqs
          · rw [hqp]
            have hdist : |inner ℝ g p.1.1 - inner ℝ g₀ p.1.1| < |inner ℝ g₀ p.1.1| :=
              hδp (lt_of_lt_of_le hg (min_le_right _ _))
            have hg_pos_norm : 0 < ‖g‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hgs.1)
            have hg0_pos_norm : 0 < ‖g₀‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hg₀_ne)
            have hin_g : inner ℝ (‖g‖⁻¹ • g) p.1.1 = ‖g‖⁻¹ * inner ℝ g p.1.1 := by
              rw [real_inner_smul_left]
            have hin_g0 : inner ℝ (‖g₀‖⁻¹ • g₀) p.1.1 = ‖g₀‖⁻¹ * inner ℝ g₀ p.1.1 := by
              rw [real_inner_smul_left]
            simp only [ltf, sub_zero, hin_g, hin_g0, sgn]
            rcases lt_or_gt_of_ne hinner_ne with hneg | hpos
            · have hg_neg : inner ℝ g p.1.1 < 0 := by
                rw [abs_of_neg hneg] at hdist
                linarith [abs_lt.mp hdist]
              have h1 : ¬ (0 ≤ ‖g‖⁻¹ * inner ℝ g p.1.1) :=
                not_le.mpr (mul_neg_of_pos_of_neg hg_pos_norm hg_neg)
              have h2 : ¬ (0 ≤ ‖g₀‖⁻¹ * inner ℝ g₀ p.1.1) :=
                not_le.mpr (mul_neg_of_pos_of_neg hg0_pos_norm hneg)
              simp [h1, h2]
            · have hg_pos : 0 < inner ℝ g p.1.1 := by
                rw [abs_of_pos hpos] at hdist
                linarith [abs_lt.mp hdist]
              have h1 : 0 ≤ ‖g‖⁻¹ * inner ℝ g p.1.1 := mul_nonneg hg_pos_norm.le hg_pos.le
              have h2 : 0 ≤ ‖g₀‖⁻¹ * inner ℝ g₀ p.1.1 := mul_nonneg hg0_pos_norm.le hpos.le
              simp [h1, h2]
          · exact hgs.2 q hqs
    obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := hsign_nbhd S fun p hp => (Finset.mem_filter.mp hp).2
    refine ⟨min δ₁ δ₂, lt_min hδ₁_pos hδ₂_pos, fun g hg_compl hdist => ?_⟩
    have hd1 : dist (Ψ L t g) psi0 < η / 2 :=
      hδ₁ hg_compl (lt_of_lt_of_le hdist (min_le_left _ _))
    have hd2 := (hδ₂ g (lt_of_lt_of_le hdist (min_le_right _ _))).2
    have hor_S : QMemLearner.oracle (‖g‖⁻¹ • g) (L.ctrl t) psiS =
        QMemLearner.oracle (‖g₀‖⁻¹ • g₀) (L.ctrl t) psiS := by
      change oracleCLM (‖g‖⁻¹ • g) (L.ctrl t) (∑ p ∈ S, lp.single 2 p (psi0 p)) =
        oracleCLM (‖g₀‖⁻¹ • g₀) (L.ctrl t) (∑ p ∈ S, lp.single 2 p (psi0 p))
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      change QMemLearner.oracle (‖g‖⁻¹ • g) (L.ctrl t) (lp.single 2 p (psi0 p)) =
        QMemLearner.oracle (‖g₀‖⁻¹ • g₀) (L.ctrl t) (lp.single 2 p (psi0 p))
      have h1 := oracle_single_eq (‖g‖⁻¹ • g) (L.ctrl t) p (psi0 p)
      have h2 := oracle_single_eq (‖g₀‖⁻¹ • g₀) (L.ctrl t) p (psi0 p)
      rw [h1, h2]
      congr 1
      simp only [QMemLearner.oraclePerm, Function.Involutive.toPerm, Equiv.coe_fn_mk, hd2 p hp]
    rw [dist_eq_norm, Ψ_succ, Ψ_succ, ← (L.V t).map_sub, (L.V t).norm_map]
    let Og := oracleCLM (‖g‖⁻¹ • g) (L.ctrl t)
    let Og0 := oracleCLM (‖g₀‖⁻¹ • g₀) (L.ctrl t)
    have hsplit : QMemLearner.oracle (‖g‖⁻¹ • g) (L.ctrl t) (Ψ L t g) -
          QMemLearner.oracle (‖g₀‖⁻¹ • g₀) (L.ctrl t) (Ψ L t g₀) =
        Og (Ψ L t g - psi0) + (Og (psi0 - psiS) - Og0 (psi0 - psiS)) := by
      change Og (Ψ L t g) - Og0 psi0 = _
      have h1 : Og psiS = Og0 psiS := hor_S
      calc Og (Ψ L t g) - Og0 psi0
          = Og (Ψ L t g - psi0) + (Og psi0 - Og0 psi0) := by
            rw [map_sub]; abel
        _ = Og (Ψ L t g - psi0) + ((Og psi0 - Og psiS) - (Og0 psi0 - Og0 psiS)) := by
            rw [h1]; abel
        _ = Og (Ψ L t g - psi0) + (Og (psi0 - psiS) - Og0 (psi0 - psiS)) := by
            rw [← Og.map_sub, ← Og0.map_sub]
    rw [hsplit]
    have hn1 : ‖Og (Ψ L t g - psi0)‖ = ‖Ψ L t g - psi0‖ := oracle_norm _ _ _
    have hn2 : ‖Og (psi0 - psiS)‖ = ‖psi0 - psiS‖ := oracle_norm _ _ _
    have hn3 : ‖Og0 (psi0 - psiS)‖ = ‖psi0 - psiS‖ := oracle_norm _ _ _
    calc ‖Og (Ψ L t g - psi0) + (Og (psi0 - psiS) - Og0 (psi0 - psiS))‖
        ≤ ‖Og (Ψ L t g - psi0)‖ + ‖Og (psi0 - psiS) - Og0 (psi0 - psiS)‖ := norm_add_le _ _
      _ ≤ ‖Og (Ψ L t g - psi0)‖ + (‖Og (psi0 - psiS)‖ + ‖Og0 (psi0 - psiS)‖) :=
          add_le_add le_rfl (norm_sub_le _ _)
      _ = dist (Ψ L t g) psi0 + (‖psi0 - psiS‖ + ‖psi0 - psiS‖) := by
          rw [hn1, hn2, hn3, dist_eq_norm]
      _ < η / 2 + (η / 4 + η / 4) := add_lt_add hd1 (add_lt_add happrox happrox)
      _ = η := by ring

lemma aestronglyMeasurable_Ψ {n : ℕ} (hn : 2 ≤ n) (L : QMemLearner n) :
    ∀ t ≤ L.T, AEStronglyMeasurable (Ψ L t) (γ n) := by
  intro t ht
  classical
  have hc : ContinuousOn (Ψ L t) (badZ L)ᶜ := continuousOn_Ψ L t ht
  have hcont_sub : Continuous ((badZ L)ᶜ.domRestrict (Ψ L t)) :=
    continuousOn_iff_continuous_domRestrict.mp hc
  have hsm_sub : StronglyMeasurable ((badZ L)ᶜ.domRestrict (Ψ L t)) :=
    hcont_sub.stronglyMeasurable
  let F' : E n → lp (fun _ : (E n × Bool) × L.Ω => ℂ) 2 :=
    fun g => if hg : g ∈ (badZ L)ᶜ then (badZ L)ᶜ.domRestrict (Ψ L t) ⟨g, hg⟩ else 0
  have hsm_F' : StronglyMeasurable F' :=
    StronglyMeasurable.dite hsm_sub stronglyMeasurable_const (measurableSet_badZ L).compl
  have hae : F' =ᵐ[γ n] Ψ L t := by
    filter_upwards [compl_mem_ae_iff.mpr (γ_badZ_eq_zero hn L)] with g hg
    dsimp [F', Set.domRestrict]
    simp [hg]
  exact hsm_F'.aestronglyMeasurable.congr hae

lemma memLp_coord_of_unit {n : ℕ} {Ω : Type}
    (F : E n → lp (fun _ : (E n × Bool) × Ω => ℂ) 2)
    (hF_meas : AEStronglyMeasurable F (γ n))
    (hF_norm : ∀ g, ‖F g‖ = 1) (p : (E n × Bool) × Ω) :
    MemLp (fun g => (F g p).re) 2 (γ n) ∧ MemLp (fun g => (F g p).im) 2 (γ n) := by
  let ev := lp.evalCLM ℂ (fun _ : (E n × Bool) × Ω => ℂ) 2 p
  have hcoord : AEStronglyMeasurable (fun g => F g p) (γ n) :=
    ev.continuous.comp_aestronglyMeasurable hF_meas
  have hbound : ∀ g, ‖F g p‖ ≤ 1 := fun g =>
    (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (F g) p).trans_eq (hF_norm g)
  refine ⟨MemLp.of_bound (Complex.reCLM.continuous.comp_aestronglyMeasurable hcoord) 1
      (ae_of_all _ fun g => ?_),
    MemLp.of_bound (Complex.imCLM.continuous.comp_aestronglyMeasurable hcoord) 1
      (ae_of_all _ fun g => ?_)⟩
  · rw [Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm (F g p)).trans (hbound g)
  · rw [Real.norm_eq_abs]
    exact (Complex.abs_im_le_norm (F g p)).trans (hbound g)

lemma W_H_Ψ_le {n : ℕ} (hn : 2 ≤ n) (L : QMemLearner n) :
    ∀ t ≤ L.T, W_H (Ψ L t) ≤ (4402 : ℝ≥0∞) ^ t := by
  intro t ht
  induction t with
  | zero =>
    have hcoeff_const : ∀ (c : ℝ) (α : Fin n → ℕ),
        coeff_nd (fun _ : E n => c) α = if α = 0 then c else 0 := by
      intro c α
      unfold coeff_nd
      have h1 : ∀ g : E n, Hnd α g * c = c * (Hnd α g * Hnd (0 : Fin n → ℕ) g) := by
        intro g
        have h0 : Hnd (0 : Fin n → ℕ) g = 1 := by simp [Hnd, h1D_zero_fn]
        rw [h0, mul_one]; ring
      simp_rw [h1, integral_const_mul, Hnd_orthonormal]
      split_ifs <;> simp
    have hW_const : ∀ c : ℝ, W_real (fun _ : E n => c) = ENNReal.ofReal (c ^ 2) := by
      intro c
      unfold W_real
      rw [tsum_eq_single (0 : Fin n → ℕ)]
      · simp [hcoeff_const c 0, totalDeg]
      · intro α hα
        simp [hcoeff_const c α, hα]
    have h0 : W_H (Ψ L 0) = ENNReal.ofReal (‖L.init‖ ^ 2) := by
      unfold W_H
      have hterm : ∀ p, W_real (fun g => (Ψ L 0 g p).re) + W_real (fun g => (Ψ L 0 g p).im) =
          ENNReal.ofReal (‖L.init p‖ ^ 2) := by
        intro p
        have hre : (fun g => (Ψ L 0 g p).re) = fun _ => (L.init p).re := rfl
        have him : (fun g => (Ψ L 0 g p).im) = fun _ => (L.init p).im := rfl
        rw [hre, him, hW_const, hW_const, ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
          Complex.sq_norm, Complex.normSq_apply, sq, sq]
      simp_rw [hterm]
      have hsm : Summable (fun p => ‖L.init p‖ ^ 2) := by
        have hp2 : (2 : ENNReal).toReal = (2 : ℝ) := by norm_num
        have h := (lp.memℓp L.init).summable (p := 2) (by norm_num)
        simpa only [hp2, Real.rpow_two] using h
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun p => sq_nonneg _) hsm]
      congr 1
      exact (lp_norm_sq_eq_tsum L.init).symm
    rw [h0, L.init_norm, one_pow, ENNReal.ofReal_one, pow_zero]
  | succ t ih =>
    have ht_le : t ≤ L.T := Nat.le_of_succ_le ht
    let G : E n → lp (fun _ : (E n × Bool) × L.Ω => ℂ) 2 :=
      fun g => QMemLearner.oracle (‖g‖⁻¹ • g) (L.ctrl t) (Ψ L t g)
    have hΨ1_eq : Ψ L (t + 1) = fun g => L.V t (G g) := rfl
    have hG_eq : G = fun g => (L.V t).symm (Ψ L (t + 1) g) := by
      ext g p; change G g p = ((L.V t).symm (L.V t (G g))) p
      rw [(L.V t).symm_apply_apply]
    have hG_meas : AEStronglyMeasurable G (γ n) := by
      rw [hG_eq]
      exact (L.V t).symm.continuous.comp_aestronglyMeasurable (aestronglyMeasurable_Ψ hn L (t + 1) ht)
    have hG_norm : ∀ g, ‖G g‖ = 1 := fun g => by
      dsimp [G]; rw [oracle_norm, Ψ_norm]
    have hG_mem : ∀ p, MemLp (fun g => (G g p).re) 2 (γ n) ∧
        MemLp (fun g => (G g p).im) 2 (γ n) :=
      memLp_coord_of_unit G hG_meas hG_norm
    have hΨ1_mem : ∀ p, MemLp (fun g => (Ψ L (t + 1) g p).re) 2 (γ n) ∧
        MemLp (fun g => (Ψ L (t + 1) g p).im) 2 (γ n) :=
      memLp_coord_of_unit (Ψ L (t + 1)) (aestronglyMeasurable_Ψ hn L (t + 1) ht) (Ψ_norm L (t + 1))
    have hΨ_mem : ∀ p, MemLp (fun g => (Ψ L t g p).re) 2 (γ n) ∧
        MemLp (fun g => (Ψ L t g p).im) 2 (γ n) :=
      memLp_coord_of_unit (Ψ L t) (aestronglyMeasurable_Ψ hn L t ht_le) (Ψ_norm L t)
    calc W_H (Ψ L (t + 1))
        = W_H G := W_H_comp_isom (L.V t) G hG_meas hG_norm hG_mem hΨ1_mem
      _ ≤ 4402 * W_H (Ψ L t) := W_H_oracle_le (L.ctrl t) (Ψ L t) hΨ_mem
      _ ≤ 4402 * (4402 : ℝ≥0∞) ^ t := mul_le_mul_of_nonneg_left (ih ht_le) bot_le
      _ = (4402 : ℝ≥0∞) ^ (t + 1) := by rw [pow_succ']

lemma H_parseval_tail_le {n : ℕ} (hn : 2 ≤ n) (L : QMemLearner n) (d : ℕ) :
    let v : (Fin n → ℕ) → lp (fun _ : (E n × Bool) × L.Ω => ℂ) 2 :=
      fun α => ∫ g : E n, (Hnd α g : ℂ) • Ψ L L.T g ∂(γ n)
    let L_deg : E n → lp (fun _ : (E n × Bool) × L.Ω => ℂ) 2 :=
      fun g => ∑ α ∈ I_deg n d, (Hnd α g : ℂ) • v α
    let H_rem : E n → lp (fun _ : (E n × Bool) × L.Ω => ℂ) 2 :=
      fun g => Ψ L L.T g - L_deg g
    Integrable (fun g => ‖L_deg g‖ ^ 2) (γ n) ∧
    (∫ g : E n, ‖L_deg g‖ ^ 2 ∂(γ n) ≤ 1) ∧
    Integrable (fun g => ‖H_rem g‖ ^ 2) (γ n) ∧
    ENNReal.ofReal ((d + 2 : ℝ) ^ (1 / 4 : ℝ) * ∫ g : E n, ‖H_rem g‖ ^ 2 ∂(γ n)) ≤
      W_H (Ψ L L.T) := by
  intro v L_deg H_rem
  have hΨ_meas : AEStronglyMeasurable (Ψ L L.T) (γ n) :=
    aestronglyMeasurable_Ψ hn L L.T le_rfl
  have hΨ_norm : ∀ g, ‖Ψ L L.T g‖ = 1 := Ψ_norm L L.T
  have hΨ_mem : ∀ p, MemLp (fun g => (Ψ L L.T g p).re) 2 (γ n) ∧
      MemLp (fun g => (Ψ L L.T g p).im) 2 (γ n) :=
    memLp_coord_of_unit (Ψ L L.T) hΨ_meas hΨ_norm
  have hL_cont : Continuous L_deg := by
    refine continuous_finsetSum _ fun α _ => ?_
    exact (Complex.continuous_ofReal.comp (continuous_Hnd α)).smul continuous_const
  have hL_sq_int : Integrable (fun g => ‖L_deg g‖ ^ 2) (γ n) := by
    let C : ℝ := (I_deg n d).card
    have hdom : Integrable (fun g : E n => C * ∑ α ∈ I_deg n d, (Hnd α g) ^ 2 * ‖v α‖ ^ 2) (γ n) :=
      (integrable_finsetSum _ fun α _ =>
        ((integrable_Hnd_mul_Hnd α α).congr (ae_of_all _ fun g => (sq (Hnd α g)).symm)).mul_const _).const_mul C
    refine hdom.mono' (hL_cont.norm.pow 2).aestronglyMeasurable (ae_of_all _ fun g => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hnorm_sum : ‖L_deg g‖ ≤ ∑ α ∈ I_deg n d, (1 : ℝ) * ‖(Hnd α g : ℂ) • v α‖ := by
      dsimp only [L_deg]
      simpa using norm_sum_le (I_deg n d) fun α => (Hnd α g : ℂ) • v α
    have hsq : ‖L_deg g‖ ^ 2 ≤ (∑ α ∈ I_deg n d, (1 : ℝ) * ‖(Hnd α g : ℂ) • v α‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm_sum 2
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (I_deg n d)
      (fun _ : Fin n → ℕ => (1 : ℝ)) (fun α => ‖(Hnd α g : ℂ) • v α‖)
    have hterm : ∀ α, ‖(Hnd α g : ℂ) • v α‖ ^ 2 = (Hnd α g) ^ 2 * ‖v α‖ ^ 2 := by
      intro α; rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    simp_rw [hterm] at hcs
    simp only [Finset.sum_const, nsmul_eq_mul, one_pow, mul_one] at hcs
    exact hsq.trans hcs
  have hL_memLp : MemLp L_deg 2 (γ n) :=
    ((memLp_two_iff_integrable_sq hL_cont.norm.aestronglyMeasurable).mpr hL_sq_int).mono'
      hL_cont.aestronglyMeasurable (ae_of_all _ fun g => by simp)
  have hΨ_memLp : MemLp (Ψ L L.T) 2 (γ n) :=
    MemLp.of_bound hΨ_meas 1 (ae_of_all _ fun g => (hΨ_norm g).le)
  have hrem_memLp : MemLp H_rem 2 (γ n) := hΨ_memLp.sub hL_memLp
  have hrem_sq_int : Integrable (fun g => ‖H_rem g‖ ^ 2) (γ n) := hrem_memLp.norm.integrable_sq
  have hv_int : ∀ α : Fin n → ℕ, Integrable (fun g : E n => (Hnd α g : ℂ) • Ψ L L.T g) (γ n) := by
    intro α
    have hsm : AEStronglyMeasurable (fun g : E n => (Hnd α g : ℂ) • Ψ L L.T g) (γ n) :=
      (Complex.continuous_ofReal.comp (continuous_Hnd α)).aestronglyMeasurable.smul hΨ_meas
    refine (memLp_Hnd α).integrable one_le_two |>.abs.mono' hsm (ae_of_all _ fun g => ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, hΨ_norm g, mul_one]
  have hv_coord : ∀ α p, (v α) p =
      (coeff_nd (fun g => (Ψ L L.T g p).re) α : ℂ) +
        (coeff_nd (fun g => (Ψ L L.T g p).im) α : ℂ) * Complex.I := by
    intro α p
    let ev := lp.evalCLM ℂ (fun _ : (E n × Bool) × L.Ω => ℂ) 2 p
    have hev : (v α) p = ∫ g : E n, (Hnd α g : ℂ) * Ψ L L.T g p ∂(γ n) := by
      dsimp only [v]
      change ev (∫ g : E n, (Hnd α g : ℂ) • Ψ L L.T g ∂(γ n)) = _
      rw [← ev.integral_comp_comm (hv_int α)]
      rfl
    have hint_c : Integrable (fun g : E n => (Hnd α g : ℂ) * Ψ L L.T g p) (γ n) :=
      ev.integrable_comp (hv_int α)
    have hre : (∫ g : E n, (Hnd α g : ℂ) * Ψ L L.T g p ∂(γ n)).re =
        coeff_nd (fun g => (Ψ L L.T g p).re) α := by
      have hcomm := Complex.reCLM.integral_comp_comm hint_c
      change ∫ g : E n, ((Hnd α g : ℂ) * Ψ L L.T g p).re ∂(γ n) =
        (∫ g : E n, (Hnd α g : ℂ) * Ψ L L.T g p ∂(γ n)).re at hcomm
      rw [← hcomm]
      refine integral_congr_ae (ae_of_all _ fun g => ?_)
      simp [Complex.mul_re]
    have him : (∫ g : E n, (Hnd α g : ℂ) * Ψ L L.T g p ∂(γ n)).im =
        coeff_nd (fun g => (Ψ L L.T g p).im) α := by
      have hcomm := Complex.imCLM.integral_comp_comm hint_c
      change ∫ g : E n, ((Hnd α g : ℂ) * Ψ L L.T g p).im ∂(γ n) =
        (∫ g : E n, (Hnd α g : ℂ) * Ψ L L.T g p ∂(γ n)).im at hcomm
      rw [← hcomm]
      refine integral_congr_ae (ae_of_all _ fun g => ?_)
      simp [Complex.mul_im]
    rw [hev, ← Complex.re_add_im (∫ g : E n, (Hnd α g : ℂ) * Ψ L L.T g p ∂(γ n)), hre, him]
  have hL_coord_re : ∀ p g, (L_deg g p).re = projFin (fun g => (Ψ L L.T g p).re) d g := by
    intro p g
    dsimp only [L_deg, projFin]
    rw [lp.coeFn_sum, Finset.sum_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    change (((Hnd α g : ℂ) • v α) p).re = coeff_nd (fun g => (Ψ L L.T g p).re) α * Hnd α g
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hv_coord α p]
    simp [Complex.mul_re, mul_comm]
  have hL_coord_im : ∀ p g, (L_deg g p).im = projFin (fun g => (Ψ L L.T g p).im) d g := by
    intro p g
    dsimp only [L_deg, projFin]
    rw [lp.coeFn_sum, Finset.sum_apply, Complex.im_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    change (((Hnd α g : ℂ) • v α) p).im = coeff_nd (fun g => (Ψ L L.T g p).im) α * Hnd α g
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hv_coord α p]
    simp [Complex.mul_im, mul_comm]
  have hsupp_v : ∀ α, ∀ p ∉ suppK L L.T, (v α) p = 0 := by
    intro α p hp
    have hre0 : coeff_nd (fun g => (Ψ L L.T g p).re) α = 0 := by
      unfold coeff_nd
      simp [Ψ_eq_zero_of_not_mem_suppK L L.T _ p hp]
    have him0 : coeff_nd (fun g => (Ψ L L.T g p).im) α = 0 := by
      unfold coeff_nd
      simp [Ψ_eq_zero_of_not_mem_suppK L L.T _ p hp]
    rw [hv_coord, hre0, him0]
    simp
  have hsupp_L : ∀ g, ∀ p ∉ suppK L L.T, L_deg g p = 0 := by
    intro g p hp
    dsimp only [L_deg]
    rw [lp.coeFn_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun α _ => ?_
    change ((Hnd α g : ℂ) • v α) p = 0
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hsupp_v α p hp, mul_zero]
  have hsupp_rem : ∀ g, ∀ p ∉ suppK L L.T, H_rem g p = 0 := by
    intro g p hp
    change (Ψ L L.T g - L_deg g) p = 0
    rw [lp.coeFn_sub, Pi.sub_apply, Ψ_eq_zero_of_not_mem_suppK L L.T g p hp, hsupp_L g p hp, sub_zero]
  have : Countable (↥(suppK L L.T)) := (countable_suppK L L.T).to_subtype
  have hnorm_sq_tsum : ∀ (F : E n → lp (fun _ : (E n × Bool) × L.Ω => ℂ) 2)
      (hF_meas : AEStronglyMeasurable F (γ n))
      (hF_supp : ∀ g, ∀ p ∉ suppK L L.T, F g p = 0)
      (hF_sq_int : Integrable (fun g => ‖F g‖ ^ 2) (γ n)),
      ENNReal.ofReal (∫ g : E n, ‖F g‖ ^ 2 ∂(γ n)) =
        ∑' p : ↥(suppK L L.T),
          (ENNReal.ofReal (∫ g : E n, (F g p.1).re ^ 2 ∂(γ n)) +
           ENNReal.ofReal (∫ g : E n, (F g p.1).im ^ 2 ∂(γ n))) := by
    intro F hF_meas hF_supp hF_sq_int
    rw [ofReal_integral_eq_lintegral_ofReal hF_sq_int (ae_of_all _ fun _ => sq_nonneg _)]
    have hpt : ∀ g : E n, ENNReal.ofReal (‖F g‖ ^ 2) =
        ∑' p : ↥(suppK L L.T),
          (ENNReal.ofReal ((F g p.1).re ^ 2) + ENNReal.ofReal ((F g p.1).im ^ 2)) := by
      intro g
      have hp2 : (2 : ENNReal).toReal = (2 : ℝ) := by norm_num
      have hsm : Summable fun p => ‖F g p‖ ^ 2 := by
        have h2 := (lp.memℓp (F g)).summable (p := 2) (by norm_num)
        simpa only [hp2, Real.rpow_two] using h2
      rw [lp_norm_sq_eq_tsum, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hsm]
      have hsub : (∑' p : (E n × Bool) × L.Ω, ENNReal.ofReal (‖F g p‖ ^ 2)) =
          ∑' p : ↥(suppK L L.T), ENNReal.ofReal (‖F g p.1‖ ^ 2) := by
        rw [tsum_subtype (suppK L L.T) (fun p => ENNReal.ofReal (‖F g p‖ ^ 2))]
        refine tsum_congr fun p => ?_
        by_cases hp : p ∈ suppK L L.T
        · simp [Set.indicator_of_mem hp]
        · simp [Set.indicator_of_notMem hp, hF_supp g p hp]
      rw [hsub]
      refine tsum_congr fun p => ?_
      rw [Complex.sq_norm, Complex.normSq_apply, ← sq, ← sq,
        ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    simp_rw [hpt]
    have hmeas_term : ∀ p : ↥(suppK L L.T),
        AEMeasurable (fun g => ENNReal.ofReal ((F g p.1).re ^ 2) +
          ENNReal.ofReal ((F g p.1).im ^ 2)) (γ n) := by
      intro p
      let ev := lp.evalCLM ℂ (fun _ : (E n × Bool) × L.Ω => ℂ) 2 p.1
      have hc := ev.continuous.comp_aestronglyMeasurable hF_meas
      have hre := (Complex.reCLM.continuous.comp_aestronglyMeasurable hc).pow 2
      have him := (Complex.imCLM.continuous.comp_aestronglyMeasurable hc).pow 2
      exact (hre.aemeasurable.ennreal_ofReal).add (him.aemeasurable.ennreal_ofReal)
    rw [lintegral_tsum hmeas_term]
    refine tsum_congr fun p => ?_
    let ev := lp.evalCLM ℂ (fun _ : (E n × Bool) × L.Ω => ℂ) 2 p.1
    have hc := ev.continuous.comp_aestronglyMeasurable hF_meas
    have hre_m : AEStronglyMeasurable (fun g => (F g p.1).re) (γ n) :=
      Complex.reCLM.continuous.comp_aestronglyMeasurable hc
    have him_m : AEStronglyMeasurable (fun g => (F g p.1).im) (γ n) :=
      Complex.imCLM.continuous.comp_aestronglyMeasurable hc
    have hre_le : ∀ g, (F g p.1).re ^ 2 ≤ ‖F g‖ ^ 2 := fun g => by
      have h1 : |(F g p.1).re| ≤ ‖F g p.1‖ := Complex.abs_re_le_norm _
      have h2 : ‖F g p.1‖ ≤ ‖F g‖ := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (F g) p.1
      have h3 : |(F g p.1).re| ≤ ‖F g‖ := h1.trans h2
      nlinarith [sq_abs ((F g p.1).re), norm_nonneg (F g), abs_nonneg ((F g p.1).re)]
    have him_le : ∀ g, (F g p.1).im ^ 2 ≤ ‖F g‖ ^ 2 := fun g => by
      have h1 : |(F g p.1).im| ≤ ‖F g p.1‖ := Complex.abs_im_le_norm _
      have h2 : ‖F g p.1‖ ≤ ‖F g‖ := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (F g) p.1
      have h3 : |(F g p.1).im| ≤ ‖F g‖ := h1.trans h2
      nlinarith [sq_abs ((F g p.1).im), norm_nonneg (F g), abs_nonneg ((F g p.1).im)]
    have hre_int : Integrable (fun g => (F g p.1).re ^ 2) (γ n) :=
      hF_sq_int.mono' (hre_m.pow 2) (ae_of_all _ fun g => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hre_le g)
    have him_int : Integrable (fun g => (F g p.1).im ^ 2) (γ n) :=
      hF_sq_int.mono' (him_m.pow 2) (ae_of_all _ fun g => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact him_le g)
    have hre_am : AEMeasurable (fun g => ENNReal.ofReal ((F g p.1).re ^ 2)) (γ n) :=
      (hre_m.pow 2).aemeasurable.ennreal_ofReal
    rw [lintegral_add_left' hre_am (fun g => ENNReal.ofReal ((F g p.1).im ^ 2)),
      ← ofReal_integral_eq_lintegral_ofReal hre_int (ae_of_all _ fun _ => sq_nonneg _),
      ← ofReal_integral_eq_lintegral_ofReal him_int (ae_of_all _ fun _ => sq_nonneg _)]
  have hΨ_sq_int : Integrable (fun g => ‖Ψ L L.T g‖ ^ 2) (γ n) :=
    Integrable.of_bound (hΨ_meas.norm.pow 2) 1 (ae_of_all _ fun g => by
      rw [Real.norm_eq_abs, hΨ_norm g]; norm_num)
  have hΨ_int_eq_one : ∫ g : E n, ‖Ψ L L.T g‖ ^ 2 ∂(γ n) = 1 := by
    have heq : (fun g : E n => ‖Ψ L L.T g‖ ^ 2) = fun _ => (1 : ℝ) := by
      ext g; rw [hΨ_norm g, one_pow]
    rw [heq, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  have hL_le_one : ∫ g : E n, ‖L_deg g‖ ^ 2 ∂(γ n) ≤ 1 := by
    rw [← ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1), ← hΨ_int_eq_one,
      hnorm_sq_tsum L_deg hL_cont.aestronglyMeasurable hsupp_L hL_sq_int,
      hnorm_sq_tsum (Ψ L L.T) hΨ_meas (fun g p hp => Ψ_eq_zero_of_not_mem_suppK L L.T g p hp) hΨ_sq_int]
    refine ENNReal.tsum_le_tsum fun p => add_le_add (ENNReal.ofReal_le_ofReal ?_) (ENNReal.ofReal_le_ofReal ?_)
    · simp_rw [hL_coord_re p.1]
      rw [integral_projFin_sq _ d, ← (parseval_nd (hΨ_mem p.1).1).tsum_eq]
      exact (parseval_nd (hΨ_mem p.1).1).summable.sum_le_tsum (I_deg n d) (fun _ _ => sq_nonneg _)
    · simp_rw [hL_coord_im p.1]
      rw [integral_projFin_sq _ d, ← (parseval_nd (hΨ_mem p.1).2).tsum_eq]
      exact (parseval_nd (hΨ_mem p.1).2).summable.sum_le_tsum (I_deg n d) (fun _ _ => sq_nonneg _)
  have hW_tail_scalar : ∀ (u : E n → ℝ), MemLp u 2 (γ n) →
      ENNReal.ofReal ((d + 2 : ℝ) ^ (1 / 4 : ℝ) * ∫ g : E n, (u g - projFin u d g) ^ 2 ∂(γ n)) ≤
        W_real u := by
    intro u hu
    let r : E n → ℝ := fun g => u g - projFin u d g
    have hr : MemLp r 2 (γ n) := hu.sub (P_Hnd_memLp (projFin_mem_P_Hnd u d))
    have hcoeff_r : ∀ α : Fin n → ℕ,
        coeff_nd r α = if α ∈ I_deg n d then 0 else coeff_nd u α := by
      intro α
      split_ifs with hα
      · exact integral_projFin_orth hu d (Submodule.subset_span ⟨α, hα, rfl⟩)
      · rw [coeff_nd_sub hu (P_Hnd_memLp (projFin_mem_P_Hnd u d))]
        have hproj0 : coeff_nd (projFin u d) α = 0 := by
          unfold coeff_nd projFin
          have heq : (fun g : E n => Hnd α g * ∑ β ∈ I_deg n d, coeff_nd u β * Hnd β g) =
              fun g => ∑ β ∈ I_deg n d, coeff_nd u β * (Hnd α g * Hnd β g) := by
            ext g; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun β _ => by ring
          rw [heq, integral_finsetSum _ fun β _ => (integrable_Hnd_mul_Hnd α β).const_mul _]
          refine Finset.sum_eq_zero fun β hβ => ?_
          rw [integral_const_mul, Hnd_orthonormal, if_neg (fun heq => hα (by subst heq; exact hβ)), mul_zero]
        rw [hproj0, sub_zero]
    rw [← (parseval_nd hr).tsum_eq]
    have hsm := (parseval_nd hr).summable.mul_left ((d + 2 : ℝ) ^ (1 / 4 : ℝ))
    rw [← tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hsm]
    refine ENNReal.tsum_le_tsum fun α => ENNReal.ofReal_le_ofReal ?_
    rw [hcoeff_r α]
    split_ifs with hα
    · simp; positivity
    · rw [mem_I_deg, not_le] at hα
      have hbase : (d + 2 : ℝ) ≤ (1 + (totalDeg α : ℝ)) := by
        have h1 : d + 2 ≤ 1 + totalDeg α := by omega
        exact_mod_cast h1
      have hpow : (d + 2 : ℝ) ^ (1 / 4 : ℝ) ≤ (1 + (totalDeg α : ℝ)) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hbase (by norm_num)
      exact mul_le_mul_of_nonneg_right hpow (sq_nonneg _)
  have htail_bound : ENNReal.ofReal ((d + 2 : ℝ) ^ (1 / 4 : ℝ) * ∫ g : E n, ‖H_rem g‖ ^ 2 ∂(γ n)) ≤
      W_H (Ψ L L.T) := by
    rw [ENNReal.ofReal_mul (by positivity),
      hnorm_sq_tsum H_rem (hΨ_meas.sub hL_cont.aestronglyMeasurable) hsupp_rem hrem_sq_int,
      ← ENNReal.tsum_mul_left]
    have hW_sub : (∑' p : ↥(suppK L L.T),
          (W_real (fun g => (Ψ L L.T g p.1).re) + W_real (fun g => (Ψ L L.T g p.1).im))) ≤
        W_H (Ψ L L.T) := by
      have hts := tsum_subtype (suppK L L.T)
        (fun p => W_real (fun g => (Ψ L L.T g p).re) + W_real (fun g => (Ψ L L.T g p).im))
      calc ∑' p : ↥(suppK L L.T),
            (W_real (fun g => (Ψ L L.T g p.1).re) + W_real (fun g => (Ψ L L.T g p.1).im))
          = ∑' p : (E n × Bool) × L.Ω, (suppK L L.T).indicator
              (fun p => W_real (fun g => (Ψ L L.T g p).re) + W_real (fun g => (Ψ L L.T g p).im)) p :=
            hts
        _ ≤ W_H (Ψ L L.T) := by
            unfold W_H
            refine ENNReal.tsum_le_tsum fun p => ?_
            by_cases hp : p ∈ suppK L L.T
            · simp [Set.indicator_of_mem hp]
            · simp [Set.indicator_of_notMem hp]
    refine le_trans ?_ hW_sub
    refine ENNReal.tsum_le_tsum fun p => ?_
    rw [mul_add]
    have hre_int_eq : ∫ g : E n, (H_rem g p.1).re ^ 2 ∂(γ n) =
        ∫ g : E n, ((Ψ L L.T g p.1).re - projFin (fun g => (Ψ L L.T g p.1).re) d g) ^ 2 ∂(γ n) :=
      integral_congr_ae (ae_of_all _ fun g => by
        dsimp only [H_rem]
        rw [lp.coeFn_sub, Pi.sub_apply, Complex.sub_re, hL_coord_re p.1 g])
    have him_int_eq : ∫ g : E n, (H_rem g p.1).im ^ 2 ∂(γ n) =
        ∫ g : E n, ((Ψ L L.T g p.1).im - projFin (fun g => (Ψ L L.T g p.1).im) d g) ^ 2 ∂(γ n) :=
      integral_congr_ae (ae_of_all _ fun g => by
        dsimp only [H_rem]
        rw [lp.coeFn_sub, Pi.sub_apply, Complex.sub_im, hL_coord_im p.1 g])
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      hre_int_eq, him_int_eq]
    exact add_le_add (hW_tail_scalar _ (hΨ_mem p.1).1) (hW_tail_scalar _ (hΨ_mem p.1).2)
  exact ⟨hL_sq_int, hL_le_one, hrem_sq_int, htail_bound⟩

lemma disagree_symm {n : ℕ} (f g : E n → ℤ) : disagree f g = disagree g f := by
  unfold disagree
  have heq : {x : E n | f x ≠ g x} = {x : E n | g x ≠ f x} := by
    ext x; exact ne_comm
  rw [heq]

lemma disagree_triangle {n : ℕ} (f g h : E n → ℤ) :
    disagree f h ≤ disagree f g + disagree g h := by
  unfold disagree
  have hsub : {x : E n | f x ≠ h x} ⊆ {x : E n | f x ≠ g x} ∪ {x : E n | g x ≠ h x} := by
    intro x hx
    by_cases hfg : f x = g x
    · right; intro hgh; apply hx; exact hfg.trans hgh
    · left; exact hfg
  have hle : ProbabilityTheory.stdGaussian (E n) {x : E n | f x ≠ h x} ≤
      ProbabilityTheory.stdGaussian (E n) {x : E n | f x ≠ g x} +
        ProbabilityTheory.stdGaussian (E n) {x : E n | g x ≠ h x} :=
    (measure_mono hsub).trans (measure_union_le _ _)
  have hne1 : ProbabilityTheory.stdGaussian (E n) {x : E n | f x ≠ g x} ≠ ⊤ := measure_ne_top _ _
  have hne2 : ProbabilityTheory.stdGaussian (E n) {x : E n | g x ≠ h x} ≠ ⊤ := measure_ne_top _ _
  calc (ProbabilityTheory.stdGaussian (E n) {x : E n | f x ≠ h x}).toReal
      ≤ (ProbabilityTheory.stdGaussian (E n) {x : E n | f x ≠ g x} +
          ProbabilityTheory.stdGaussian (E n) {x : E n | g x ≠ h x}).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hne1, hne2⟩) hle
    _ = (ProbabilityTheory.stdGaussian (E n) {x : E n | f x ≠ g x}).toReal +
          (ProbabilityTheory.stdGaussian (E n) {x : E n | g x ≠ h x}).toReal :=
        ENNReal.toReal_add hne1 hne2

lemma pos_op_diff_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {E_op : H →L[ℂ] H} (hE : E_op.IsPositive)
    (hE_le : ∀ z : H, RCLike.re (inner ℂ z (E_op z)) ≤ ‖z‖ ^ 2)
    {x y : H} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    |RCLike.re (inner ℂ x (E_op x)) - RCLike.re (inner ℂ y (E_op y))| ≤ 2 * ‖x - y‖ := by
  have hexp : RCLike.re (inner ℂ x (E_op x)) - RCLike.re (inner ℂ y (E_op y)) =
      RCLike.re (inner ℂ (x - y) (E_op x)) + RCLike.re (inner ℂ y (E_op (x - y))) := by
    have h1 : inner ℂ x (E_op x) = inner ℂ (x - y) (E_op x) + inner ℂ y (E_op x) := by
      rw [← inner_add_left, sub_add_cancel]
    have h2 : inner ℂ y (E_op x) = inner ℂ y (E_op y) + inner ℂ y (E_op (x - y)) := by
      rw [← inner_add_right, ← map_add, add_sub_cancel]
    rw [h1, h2]
    simp only [rclike_re_eq, Complex.add_re]
    ring
  have h1 : |RCLike.re (inner ℂ (x - y) (E_op x))| ≤ ‖x - y‖ := by
    have hcs := re_inner_pos_op_le hE (x - y) x
    have hle : RCLike.re (inner ℂ (x - y) (E_op (x - y))) * RCLike.re (inner ℂ x (E_op x)) ≤
        ‖x - y‖ ^ 2 := by
      calc RCLike.re (inner ℂ (x - y) (E_op (x - y))) * RCLike.re (inner ℂ x (E_op x))
          ≤ ‖x - y‖ ^ 2 * ‖x‖ ^ 2 :=
            mul_le_mul (hE_le (x - y)) (hE_le x) (hE.re_inner_nonneg_right x) (sq_nonneg _)
        _ = ‖x - y‖ ^ 2 := by rw [hx, one_pow, mul_one]
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq (norm_nonneg (x - y))]
    exact Real.sqrt_le_sqrt (hcs.trans hle)
  have h2 : |RCLike.re (inner ℂ y (E_op (x - y)))| ≤ ‖x - y‖ := by
    have hcs := re_inner_pos_op_le hE y (x - y)
    have hle : RCLike.re (inner ℂ y (E_op y)) * RCLike.re (inner ℂ (x - y) (E_op (x - y))) ≤
        ‖x - y‖ ^ 2 := by
      calc RCLike.re (inner ℂ y (E_op y)) * RCLike.re (inner ℂ (x - y) (E_op (x - y)))
          ≤ ‖y‖ ^ 2 * ‖x - y‖ ^ 2 :=
            mul_le_mul (hE_le y) (hE_le (x - y)) (hE.re_inner_nonneg_right (x - y)) (sq_nonneg _)
        _ = ‖x - y‖ ^ 2 := by rw [hy, one_pow, one_mul]
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq (norm_nonneg (x - y))]
    exact Real.sqrt_le_sqrt (hcs.trans hle)
  rw [hexp]
  exact (abs_add_le _ _).trans (by linarith)

private lemma pos_op_scale {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (E_op : H →L[ℂ] H) (x : H) (hx0 : x ≠ 0) :
    RCLike.re (inner ℂ x (E_op x)) =
      ‖x‖ ^ 2 * RCLike.re (inner ℂ (‖x‖⁻¹ • x) (E_op (‖x‖⁻¹ • x))) := by
  let u : H := ‖x‖⁻¹ • x
  have hu_eq : (‖x‖ : ℂ) • u = x := by
    calc (‖x‖ : ℂ) • u
        = (‖x‖ • (1 : ℂ)) • u := by rw [Complex.real_smul, mul_one]
      _ = ‖x‖ • u := smul_one_smul ℂ ‖x‖ u
      _ = ‖x‖ • (‖x‖⁻¹ • x) := rfl
      _ = (‖x‖ * ‖x‖⁻¹) • x := smul_smul ‖x‖ ‖x‖⁻¹ x
      _ = (1 : ℝ) • x := by rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx0)]
      _ = x := one_smul ℝ x
  conv_lhs => rw [← hu_eq, map_smul, inner_smul_left, inner_smul_right]
  simp only [rclike_re_eq, Complex.conj_ofReal, Complex.re_ofReal_mul]
  ring

lemma learner_cover_and_povm {n : ℕ} (hn : 2 ≤ n) (L : QMemLearner n)
    {ε : ℝ} (hε_pos : 0 < ε) (hε_le : 3 * ε ≤ 1 / 2)
    (hsucc : ∀ w : E n, ‖w‖ = 1 → L.Succeeds w ε) (d : ℕ) :
    let v : (Fin n → ℕ) → lp (fun _ : (E n × Bool) × L.Ω => ℂ) 2 :=
      fun α => ∫ g : E n, (Hnd α g : ℂ) • Ψ L L.T g ∂(γ n)
    let L_deg : E n → lp (fun _ : (E n × Bool) × L.Ω => ℂ) 2 :=
      fun g => ∑ α ∈ I_deg n d, (Hnd α g : ℂ) • v α
    ∃ (M : ℕ) (E_op : (Fin M → Bool) →
        lp (fun _ : (E n × Bool) × L.Ω => ℂ) 2 →L[ℂ] lp (fun _ : (E n × Bool) × L.Ω => ℂ) 2)
      (Good : (Fin M → Bool) → Set (E n)),
      (∀ σ, (E_op σ).IsPositive) ∧
      (∀ σ x, RCLike.re (inner ℂ x (E_op σ x)) ≤ ‖x‖ ^ 2) ∧
      (∀ x : lp (fun _ : (E n × Bool) × L.Ω => ℂ) 2,
        ∑ σ : Fin M → Bool, RCLike.re (inner ℂ x (E_op σ x)) = ‖x‖ ^ 2) ∧
      (∀ σ, MeasurableSet (Good σ)) ∧
      ((64 / 100 : ℝ) < ∑ σ : Fin M → Bool,
        ∫ g in Good σ, RCLike.re (inner ℂ (Ψ L L.T g) (E_op σ (Ψ L L.T g))) ∂(γ n)) ∧
      (∀ σ, Integrable (fun g : E n => RCLike.re (inner ℂ (L_deg g) (E_op σ (L_deg g)))) (γ n) ∧
        ∫ g in Good σ, RCLike.re (inner ℂ (L_deg g) (E_op σ (L_deg g))) ∂(γ n) ≤
          (Module.finrank ℝ (V_d n d) : ℝ) * (6 * Real.pi * ε) ^ (n - 1) *
            ∫ g : E n, RCLike.re (inner ℂ (L_deg g) (E_op σ (L_deg g))) ∂(γ n)) := by
  intro v L_deg
  let S_good : Set (Metric.sphere (0 : E n) 1) := {ω | ω.1 ∉ badZ L}
  have hS_good_cone : (cone S_good)ᶜ ⊆ badZ L := by
    intro g hg
    by_cases hg0 : g = 0
    · rw [hg0]; exact Or.inl rfl
    · by_contra hnot
      apply hg
      refine ⟨hg0, ?_⟩
      let u : Metric.sphere (0 : E n) 1 :=
        ⟨‖g‖⁻¹ • g, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hg0)⟩
      refine ⟨u, ?_, rfl⟩
      change ‖g‖⁻¹ • g ∉ badZ L
      intro hbad
      rcases hbad with h0 | hbi
      · rw [Set.mem_singleton_iff] at h0
        have hnorm1 : ‖(‖g‖⁻¹ : ℝ) • g‖ = 1 := norm_smul_inv_norm hg0
        rw [h0, norm_zero] at hnorm1; norm_num at hnorm1
      · rw [Set.mem_iUnion₂] at hbi
        rcases hbi with ⟨x, hx, hinner⟩
        change inner ℝ (‖g‖⁻¹ • g) x = 0 at hinner
        have hmul : inner ℝ (‖g‖⁻¹ • g) x = ‖g‖⁻¹ * inner ℝ g x := real_inner_smul_left _ _ _
        have hpos : ‖g‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr hg0)
        rw [hmul, mul_eq_zero] at hinner
        rcases hinner with hinv | hgx
        · exact hpos hinv
        · exact hnot (Or.inr (Set.mem_biUnion hx hgx))
  have hcone_full : γ n (cone S_good) = 1 := by
    have hcomp0 : γ n (cone S_good)ᶜ = 0 :=
      measure_mono_null hS_good_cone (γ_badZ_eq_zero hn L)
    have hmeas : MeasurableSet (cone S_good) := by
      have hSm : MeasurableSet S_good := by
        have : S_good = Subtype.val ⁻¹' (badZ L)ᶜ := rfl
        rw [this]
        exact (measurableSet_badZ L).compl.preimage measurable_subtype_coe
      exact measurableSet_cone hSm
    have hsum := measure_add_measure_compl hmeas (μ := γ n)
    rw [hcomp0, add_zero, measure_univ] at hsum
    exact hsum
  have hcont_ψ := continuousOn_Ψ L L.T le_rfl
  have hball_ex : ∀ ω ∈ S_good, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 2 * ε ∧
      ∀ u ∈ (badZ L)ᶜ, dist u ω.1 < δ → ‖Ψ L L.T u - Ψ L L.T ω.1‖ < 1 / 1000 := by
    intro ω hω
    obtain ⟨δ', hδ'_pos, hδ'⟩ := Metric.continuousWithinAt_iff.mp (hcont_ψ ω.1 hω) (1 / 1000) (by norm_num)
    refine ⟨min δ' (2 * ε), lt_min hδ'_pos (by linarith), min_le_right _ _, fun u hu hdu => ?_⟩
    rw [← dist_eq_norm]
    exact hδ' hu (lt_of_lt_of_le hdu (min_le_left _ _))
  choose δ_fun hδ_pos hδ_le hδ_diff using fun ω : S_good => hball_ex ω.1 ω.2
  let B_sub : S_good → Set (Metric.sphere (0 : E n) 1) :=
    fun ω => {u : Metric.sphere (0 : E n) 1 | dist u.1 ω.1.1 < δ_fun ω}
  have hB_open : ∀ ω : S_good, IsOpen (B_sub ω) := fun ω =>
    Metric.isOpen_ball.preimage continuous_subtype_val
  obtain ⟨T_set, hTc, hT_cov⟩ :=
    TopologicalSpace.isOpen_iUnion_countable B_sub hB_open
  have hS_good_sub : S_good ⊆ ⋃ ω ∈ T_set, B_sub ω := by
    intro u hu
    rw [hT_cov, Set.mem_iUnion]
    exact ⟨⟨u, hu⟩, by simp [B_sub, hδ_pos ⟨u, hu⟩]⟩
  have hcone_sub : cone S_good ⊆ ⋃ ω ∈ T_set, cone (B_sub ω) := by
    intro g hg
    rcases hg with ⟨hg0, u, hu, hgu⟩
    have huU := hS_good_sub hu
    rw [Set.mem_iUnion₂] at huU
    rcases huU with ⟨ω, hωT, huB⟩
    exact Set.mem_biUnion hωT ⟨hg0, u, huB, hgu⟩
  have hT_ne : T_set.Nonempty := by
    by_contra hTe
    rw [Set.not_nonempty_iff_eq_empty] at hTe
    have hcone_e : cone S_good = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro g hg
      have hg' := hcone_sub hg
      simp [hTe] at hg'
    rw [hcone_e, measure_empty] at hcone_full
    norm_num at hcone_full
  have : Nonempty T_set := hT_ne.to_subtype
  have : Countable T_set := hTc.to_subtype
  obtain ⟨seq, hseq_surj⟩ := exists_surjective_nat T_set
  let covB : ℕ → Set (Metric.sphere (0 : E n) 1) := fun k => B_sub (seq k).1
  let ω_seq : ℕ → Metric.sphere (0 : E n) 1 := fun k => (seq k).1.1
  have hcov_cone : cone S_good ⊆ ⋃ k : ℕ, cone (covB k) := by
    intro g hg
    have hg1 := hcone_sub hg
    rw [Set.mem_iUnion₂] at hg1
    rcases hg1 with ⟨ω, hωT, hgω⟩
    obtain ⟨k, hk⟩ := hseq_surj ⟨ω, hωT⟩
    exact Set.mem_iUnion.mpr ⟨k, by dsimp [covB]; rw [hk]; exact hgω⟩
  let accCone : ℕ → Set (E n) := fun M => ⋃ j ∈ Finset.range M, cone (covB j)
  have hacc_mono : Monotone accCone := fun i j hij =>
    Set.iUnion₂_mono' fun k hk => ⟨k, Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) hij), Set.Subset.rfl⟩
  have hacc_union : ⋃ M : ℕ, accCone M = ⋃ k : ℕ, cone (covB k) := by
    ext g
    simp only [accCone, Set.mem_iUnion, Finset.mem_range, exists_prop]
    exact ⟨fun ⟨_, j, _, hj⟩ => ⟨j, hj⟩, fun ⟨j, hj⟩ => ⟨j + 1, j, Nat.lt_succ_self j, hj⟩⟩
  have hlim_one : γ n (⋃ M : ℕ, accCone M) = 1 := by
    refine le_antisymm (prob_le_one) ?_
    rw [← hcone_full, hacc_union]
    exact measure_mono hcov_cone
  have htend_cov : Filter.Tendsto (fun M => γ n (accCone M)) Filter.atTop (𝓝 1) := by
    rw [← hlim_one]
    exact MeasureTheory.tendsto_measure_iUnion_atTop hacc_mono
  have h99_lt : (99 / 100 : ℝ≥0∞) < 1 := by
    have h99_eq : (99 / 100 : ℝ≥0∞) = ENNReal.ofReal (99 / 100 : ℝ) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
    rw [h99_eq, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr (by norm_num)
  obtain ⟨M, hM_gt⟩ := ((tendsto_order.mp htend_cov).1 (99 / 100 : ℝ≥0∞) h99_lt).exists
  have hM_real : (99 / 100 : ℝ) < (γ n).real (accCone M) := by
    rw [Measure.real]
    have h99 : ((99 / 100 : ℝ≥0∞)).toReal = (99 / 100 : ℝ) := by
      rw [ENNReal.toReal_div]; norm_num
    rw [← h99]
    exact (ENNReal.toReal_strict_mono (measure_ne_top _ _)) hM_gt
  -- Finite index `i : Fin M`
  let B : Fin M → Set (Metric.sphere (0 : E n) 1) := fun i => covB i.1
  let ω_c : Fin M → Metric.sphere (0 : E n) 1 := fun i => ω_seq i.1
  have hB_open_fin : ∀ i : Fin M, IsOpen (B i) := fun i => hB_open _
  have hB_meas_fin : ∀ i : Fin M, MeasurableSet (B i) := fun i => (hB_open_fin i).measurableSet
  have hω_not_bad : ∀ i : Fin M, (ω_c i).1 ∉ badZ L := fun i => (seq i.1).1.2
  have hω_norm : ∀ i : Fin M, ‖(ω_c i).1‖ = 1 := fun i => mem_sphere_zero_iff_norm.mp (ω_c i).2
  have hB_prop : ∀ i : Fin M, ∀ u : Metric.sphere (0 : E n) 1, u ∈ B i →
      dist u.1 (ω_c i).1 < δ_fun (seq i.1).1 := fun _ _ hu => hu
  -- Disjointify `B` on the sphere: `D i = B i \ ⋃ j < i, B j`
  let D : Fin M → Set (Metric.sphere (0 : E n) 1) :=
    fun i => B i \ ⋃ j ∈ Finset.univ.filter (fun j : Fin M => j < i), B j
  have hD_meas : ∀ i : Fin M, MeasurableSet (D i) := fun i =>
    (hB_meas_fin i).diff (Finset.measurableSet_biUnion _ fun j _ => hB_meas_fin j)
  have hD_sub_B : ∀ i : Fin M, D i ⊆ B i := fun _ => Set.sdiff_subset
  have hD_disj : Pairwise fun i j : Fin M => Disjoint (D i) (D j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro u hui huj
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact huj.2 (Set.mem_biUnion (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩) hui.1)
    · exact hui.2 (Set.mem_biUnion (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩) huj.1)
  have hD_union : ⋃ i : Fin M, D i = ⋃ i : Fin M, B i := by
    ext u
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hui⟩; exact ⟨i, hui.1⟩
    · rintro ⟨i, hui⟩
      let S_u := Finset.univ.filter (fun k : Fin M => u ∈ B k)
      have hSu_ne : S_u.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hui⟩⟩
      let i₀ := S_u.min' hSu_ne
      have hi₀_mem := Finset.mem_filter.mp (S_u.min'_mem hSu_ne)
      refine ⟨i₀, hi₀_mem.2, ?_⟩
      intro hu_prev
      rw [Set.mem_iUnion₂] at hu_prev
      rcases hu_prev with ⟨j, hj, hju⟩
      have hlt : j < i₀ := (Finset.mem_filter.mp hj).2
      have hle : i₀ ≤ j := S_u.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hju⟩)
      exact (not_le_of_gt hlt) hle
  have hcone_D_meas : ∀ i : Fin M, MeasurableSet (cone (D i)) := fun i =>
    measurableSet_cone (hD_meas i)
  have hcone_D_disj : Pairwise fun i j : Fin M => Disjoint (cone (D i)) (cone (D j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro g hgi hgj
    rcases hgi with ⟨_, u, hu, hgu⟩
    rcases hgj with ⟨_, v', hv', hgv'⟩
    have huv : u = v' := Subtype.ext (hgu.trans hgv'.symm)
    subst huv
    exact (Set.disjoint_left.mp (hD_disj hij)) hu hv'
  have hcone_D_union : ⋃ i : Fin M, cone (D i) = accCone M := by
    ext g
    simp only [accCone, Set.mem_iUnion, Finset.mem_range, exists_prop]
    constructor
    · rintro ⟨i, hg0, u, hu, hgu⟩
      exact ⟨i.1, i.2, hg0, u, hD_sub_B i hu, hgu⟩
    · rintro ⟨j, hj, hg0, u, huB, hgu⟩
      have huU : u ∈ ⋃ i : Fin M, D i := by
        rw [hD_union]
        exact Set.mem_iUnion.mpr ⟨⟨j, hj⟩, huB⟩
      rcases Set.mem_iUnion.mp huU with ⟨i, hui⟩
      exact ⟨i, hg0, u, hui, hgu⟩
  -- Success measurable sets `S_i` for each `ω_c i`
  have hsucc_i : ∀ i : Fin M, L.Succeeds (ω_c i).1 ε := fun i => hsucc (ω_c i).1 (hω_norm i)
  choose S_meas hS_m hS_sub hS_prob using hsucc_i
  -- POVM atoms `A σ`
  let A : (Fin M → Bool) → Set L.O :=
    fun σ => ⋂ i : Fin M, if σ i then S_meas i else (S_meas i)ᶜ
  have hA_meas : ∀ σ, MeasurableSet (A σ) := fun σ =>
    MeasurableSet.iInter fun i => by split_ifs <;> [exact hS_m i; exact (hS_m i).compl]
  have hA_disj : Pairwise fun σ₁ σ₂ : Fin M → Bool => Disjoint (A σ₁) (A σ₂) := by
    intro σ₁ σ₂ hne
    rw [Set.disjoint_left]
    intro o ho1 ho2
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    have h1 := Set.mem_iInter.mp ho1 i
    have h2 := Set.mem_iInter.mp ho2 i
    cases hb1 : σ₁ i <;> cases hb2 : σ₂ i <;>
      simp only [hb1, hb2, ↓reduceIte] at h1 h2
    · exact absurd (hb1.trans hb2.symm) hi
    · exact h1 h2
    · exact h2 h1
    · exact absurd (hb1.trans hb2.symm) hi
  have hA_univ : ⋃ σ : Fin M → Bool, A σ = Set.univ := by
    ext o
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    classical
    refine ⟨fun i => decide (o ∈ S_meas i), Set.mem_iInter.mpr fun i => ?_⟩
    by_cases ho : o ∈ S_meas i <;> simp [ho]
  have hS_eq_A : ∀ i : Fin M,
      S_meas i = ⋃ σ ∈ Finset.univ.filter (fun σ : Fin M → Bool => σ i = true), A σ := by
    intro i
    ext o
    constructor
    · intro ho
      classical
      let σ : Fin M → Bool := fun j => decide (o ∈ S_meas j)
      refine Set.mem_biUnion (Finset.mem_filter.mpr ⟨Finset.mem_univ σ, decide_eq_true ho⟩) ?_
      exact Set.mem_iInter.mpr fun j => by by_cases hj : o ∈ S_meas j <;> simp [σ, hj]
    · intro ho
      rw [Set.mem_iUnion₂] at ho
      rcases ho with ⟨σ, hσ, hoA⟩
      have hσi : σ i = true := (Finset.mem_filter.mp hσ).2
      have hi := Set.mem_iInter.mp hoA i
      simpa [hσi] using hi
  -- Positive POVM operators for `A σ` and `S_meas i`
  choose E_op hE_pos hE_eval using fun σ => L.meas_povm.2 (A σ) (hA_meas σ)
  choose E_S hES_pos hES_eval using fun i => L.meas_povm.2 (S_meas i) (hS_m i)
  have hE_le : ∀ σ (x : lp (fun _ : (E n × Bool) × L.Ω => ℂ) 2),
      RCLike.re (inner ℂ x (E_op σ x)) ≤ ‖x‖ ^ 2 := by
    intro σ x
    by_cases hx0 : x = 0
    · simp [hx0]
    · let u : lp (fun _ : (E n × Bool) × L.Ω => ℂ) 2 := ‖x‖⁻¹ • x
      have hu : ‖u‖ = 1 := norm_smul_inv_norm hx0
      haveI := L.meas_povm.1 u hu
      have heval : RCLike.re (inner ℂ u (E_op σ u)) = (L.meas u (A σ)).toReal :=
        (hE_eval σ u hu).symm
      have hle1 : RCLike.re (inner ℂ u (E_op σ u)) ≤ 1 := by
        rw [heval]
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one (μ := L.meas u) (s := A σ))
      rw [pos_op_scale (E_op σ) x hx0]
      dsimp only [u] at hle1
      exact mul_le_of_le_one_right (sq_nonneg _) hle1
  have hES_le : ∀ i (x : lp (fun _ : (E n × Bool) × L.Ω => ℂ) 2),
      RCLike.re (inner ℂ x (E_S i x)) ≤ ‖x‖ ^ 2 := by
    intro i x
    by_cases hx0 : x = 0
    · simp [hx0]
    · let u : lp (fun _ : (E n × Bool) × L.Ω => ℂ) 2 := ‖x‖⁻¹ • x
      have hu : ‖u‖ = 1 := norm_smul_inv_norm hx0
      haveI := L.meas_povm.1 u hu
      have heval : RCLike.re (inner ℂ u (E_S i u)) = (L.meas u (S_meas i)).toReal :=
        (hES_eval i u hu).symm
      have hle1 : RCLike.re (inner ℂ u (E_S i u)) ≤ 1 := by
        rw [heval]
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one (μ := L.meas u) (s := S_meas i))
      rw [pos_op_scale (E_S i) x hx0]
      dsimp only [u] at hle1
      exact mul_le_of_le_one_right (sq_nonneg _) hle1
  have hE_sum_eq : ∀ x : lp (fun _ : (E n × Bool) × L.Ω => ℂ) 2,
      ∑ σ : Fin M → Bool, RCLike.re (inner ℂ x (E_op σ x)) = ‖x‖ ^ 2 := by
    intro x
    by_cases hx0 : x = 0
    · simp [hx0]
    · let u : lp (fun _ : (E n × Bool) × L.Ω => ℂ) 2 := ‖x‖⁻¹ • x
      have hu : ‖u‖ = 1 := norm_smul_inv_norm hx0
      haveI := L.meas_povm.1 u hu
      have hu_sum : ∑ σ : Fin M → Bool, RCLike.re (inner ℂ u (E_op σ u)) = 1 := by
        simp_rw [← hE_eval _ u hu]
        rw [← ENNReal.toReal_sum (fun σ _ => measure_ne_top _ _),
          ← measure_biUnion_finset (fun σ₁ _ σ₂ _ hne => hA_disj hne) (fun σ _ => hA_meas σ)]
        have hun : ⋃ σ ∈ (Finset.univ : Finset (Fin M → Bool)), A σ = Set.univ := by
          simpa using hA_univ
        rw [hun, measure_univ, ENNReal.toReal_one]
      have hscale : ∀ σ, RCLike.re (inner ℂ x (E_op σ x)) =
          ‖x‖ ^ 2 * RCLike.re (inner ℂ u (E_op σ u)) :=
        fun σ => pos_op_scale (E_op σ) x hx0
      simp_rw [hscale, ← Finset.mul_sum, hu_sum, mul_one]
  have hES_sum_eq : ∀ i : Fin M, ∀ ψ : lp (fun _ : (E n × Bool) × L.Ω => ℂ) 2, ‖ψ‖ = 1 →
      ∑ σ ∈ Finset.univ.filter (fun σ : Fin M → Bool => σ i = true),
          RCLike.re (inner ℂ ψ (E_op σ ψ)) =
        RCLike.re (inner ℂ ψ (E_S i ψ)) := by
    intro i ψ hψ
    haveI := L.meas_povm.1 ψ hψ
    simp_rw [← hE_eval _ ψ hψ]
    rw [← ENNReal.toReal_sum (fun σ _ => measure_ne_top _ _),
      ← measure_biUnion_finset (fun σ₁ _ σ₂ _ hne => hA_disj hne) (fun σ _ => hA_meas σ),
      ← hS_eq_A i, hES_eval i ψ hψ]
  let U_cov : (Fin M → Bool) → Set (Metric.sphere (0 : E n) 1) :=
    fun σ => ⋃ i ∈ Finset.univ.filter (fun i : Fin M => σ i = true), B i
  let Good : (Fin M → Bool) → Set (E n) := fun σ => cone (U_cov σ)
  have hU_meas : ∀ σ, MeasurableSet (U_cov σ) := fun σ =>
    Finset.measurableSet_biUnion _ fun i _ => hB_meas_fin i
  have hGood_meas : ∀ σ, MeasurableSet (Good σ) := fun σ =>
    measurableSet_cone (hU_meas σ)
  have hΨ_meas := aestronglyMeasurable_Ψ hn L L.T le_rfl
  have hΨ_norm := Ψ_norm L L.T
  have hf_int : ∀ σ, Integrable (fun g : E n => RCLike.re (inner ℂ (Ψ L L.T g) (E_op σ (Ψ L L.T g)))) (γ n) := by
    intro σ
    have hsm : AEStronglyMeasurable
        (fun g : E n => RCLike.re (inner ℂ (Ψ L L.T g) (E_op σ (Ψ L L.T g)))) (γ n) :=
      Complex.continuous_re.comp_aestronglyMeasurable
        (hΨ_meas.inner ((E_op σ).continuous.comp_aestronglyMeasurable hΨ_meas))
    refine Integrable.of_bound hsm 1 (ae_of_all _ fun g => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg ((hE_pos σ).re_inner_nonneg_right _)]
    exact (hE_le σ (Ψ L L.T g)).trans_eq (by rw [hΨ_norm g, one_pow])
  -- Bound from below on `∑ σ, ∫ g in Good σ, ...`
  have hlower : (64 / 100 : ℝ) < ∑ σ : Fin M → Bool,
      ∫ g in Good σ, RCLike.re (inner ℂ (Ψ L L.T g) (E_op σ (Ψ L L.T g))) ∂(γ n) := by
    have hge_disj : ∀ σ : Fin M → Bool,
        (∫ g in ⋃ i ∈ Finset.univ.filter (fun i : Fin M => σ i = true), cone (D i),
            RCLike.re (inner ℂ (Ψ L L.T g) (E_op σ (Ψ L L.T g))) ∂(γ n)) ≤
          ∫ g in Good σ, RCLike.re (inner ℂ (Ψ L L.T g) (E_op σ (Ψ L L.T g))) ∂(γ n) := by
      intro σ
      refine setIntegral_mono_set (hf_int σ).integrableOn (ae_of_all _ fun g =>
        (hE_pos σ).re_inner_nonneg_right _) (Eventually.of_forall fun g hg => ?_)
      rcases Set.mem_iUnion₂.mp hg with ⟨i, hi, hg0, u, huD, hgu⟩
      exact ⟨hg0, u, Set.mem_biUnion hi (hD_sub_B i huD), hgu⟩
    have hsum_disj : ∀ σ : Fin M → Bool,
        (∫ g in ⋃ i ∈ Finset.univ.filter (fun i : Fin M => σ i = true), cone (D i),
            RCLike.re (inner ℂ (Ψ L L.T g) (E_op σ (Ψ L L.T g))) ∂(γ n)) =
          ∑ i ∈ Finset.univ.filter (fun i : Fin M => σ i = true),
            ∫ g in cone (D i), RCLike.re (inner ℂ (Ψ L L.T g) (E_op σ (Ψ L L.T g))) ∂(γ n) := by
      intro σ
      exact integral_biUnion_finset _ (fun i _ => hcone_D_meas i)
        (fun i _ j _ hij => hcone_D_disj hij) (fun i _ => (hf_int σ).integrableOn)
    have hstep1 : ∑ i : Fin M, ∫ g in cone (D i),
          (∑ σ ∈ Finset.univ.filter (fun σ : Fin M → Bool => σ i = true),
            RCLike.re (inner ℂ (Ψ L L.T g) (E_op σ (Ψ L L.T g)))) ∂(γ n) ≤
        ∑ σ : Fin M → Bool,
          ∫ g in Good σ, RCLike.re (inner ℂ (Ψ L L.T g) (E_op σ (Ψ L L.T g))) ∂(γ n) := by
      have hcomm : ∑ i : Fin M, ∫ g in cone (D i),
            (∑ σ ∈ Finset.univ.filter (fun σ : Fin M → Bool => σ i = true),
              RCLike.re (inner ℂ (Ψ L L.T g) (E_op σ (Ψ L L.T g)))) ∂(γ n) =
          ∑ σ : Fin M → Bool,
            ∑ i ∈ Finset.univ.filter (fun i : Fin M => σ i = true),
              ∫ g in cone (D i), RCLike.re (inner ℂ (Ψ L L.T g) (E_op σ (Ψ L L.T g))) ∂(γ n) := by
        simp_rw [integral_finsetSum _ fun σ _ => (hf_int σ).integrableOn]
        calc ∑ i : Fin M, ∑ σ ∈ Finset.univ.filter (fun σ : Fin M → Bool => σ i = true),
              ∫ g in cone (D i), RCLike.re (inner ℂ (Ψ L L.T g) (E_op σ (Ψ L L.T g))) ∂(γ n)
            = ∑ i : Fin M, ∑ σ : Fin M → Bool, (if σ i = true then
                ∫ g in cone (D i), RCLike.re (inner ℂ (Ψ L L.T g) (E_op σ (Ψ L L.T g))) ∂(γ n) else 0) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [← Finset.sum_filter]
          _ = ∑ σ : Fin M → Bool, ∑ i : Fin M, (if σ i = true then
                ∫ g in cone (D i), RCLike.re (inner ℂ (Ψ L L.T g) (E_op σ (Ψ L L.T g))) ∂(γ n) else 0) :=
              Finset.sum_comm
          _ = ∑ σ : Fin M → Bool, ∑ i ∈ Finset.univ.filter (fun i : Fin M => σ i = true),
                ∫ g in cone (D i), RCLike.re (inner ℂ (Ψ L L.T g) (E_op σ (Ψ L L.T g))) ∂(γ n) := by
              refine Finset.sum_congr rfl fun σ _ => ?_
              rw [Finset.sum_filter]
      rw [hcomm]
      refine Finset.sum_le_sum fun σ _ => ?_
      rw [← hsum_disj σ]
      exact hge_disj σ
    have hpt_i : ∀ i : Fin M, ∀ᵐ g ∂(γ n), g ∈ cone (D i) →
        (664 / 1000 : ℝ) ≤ ∑ σ ∈ Finset.univ.filter (fun σ : Fin M → Bool => σ i = true),
          RCLike.re (inner ℂ (Ψ L L.T g) (E_op σ (Ψ L L.T g))) := by
      intro i
      filter_upwards [compl_mem_ae_iff.mpr (γ_badZ_eq_zero hn L)] with g hg_good hgDi
      rcases hgDi with ⟨hg0, u, huD, hgu⟩
      have hu_good : u.1 ∉ badZ L := by
        rw [hgu]
        intro hbad
        rcases hbad with h0 | hbi
        · rw [Set.mem_singleton_iff] at h0
          have h1 : ‖(‖g‖⁻¹ : ℝ) • g‖ = 1 := norm_smul_inv_norm hg0
          rw [h0, norm_zero] at h1; norm_num at h1
        · rw [Set.mem_iUnion₂] at hbi
          rcases hbi with ⟨x, hx, hinner⟩
          change inner ℝ (‖g‖⁻¹ • g) x = 0 at hinner
          have hmul : inner ℝ (‖g‖⁻¹ • g) x = ‖g‖⁻¹ * inner ℝ g x := real_inner_smul_left _ _ _
          have hpos : ‖g‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr hg0)
          rw [hmul, mul_eq_zero] at hinner
          rcases hinner with hinv | hgx
          · exact hpos hinv
          · exact hg_good (Or.inr (Set.mem_biUnion hx hgx))
      have hdist_u : dist u.1 (ω_c i).1 < δ_fun (seq i.1).1 := hB_prop i u (hD_sub_B i huD)
      have hψ_close : ‖Ψ L L.T g - Ψ L L.T (ω_c i).1‖ < 1 / 1000 := by
        have hΨ_ray : Ψ L L.T g = Ψ L L.T u.1 := by
          have hu_norm : ‖u.1‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
          dsimp [Ψ]
          rw [← hgu, hu_norm, inv_one, one_smul]
        rw [hΨ_ray]
        exact hδ_diff (seq i.1).1 u.1 hu_good hdist_u
      rw [hES_sum_eq i (Ψ L L.T g) (hΨ_norm g)]
      have hdiff_E := pos_op_diff_le (hES_pos i) (hES_le i) (hΨ_norm g) (hΨ_norm (ω_c i).1)
      have hcenter_ge : (2 / 3 : ℝ) ≤ RCLike.re (inner ℂ (Ψ L L.T (ω_c i).1) (E_S i (Ψ L L.T (ω_c i).1))) := by
        have hψ_eq : Ψ L L.T (ω_c i).1 = L.stateAt (ω_c i).1 L.T := by
          dsimp [Ψ]; rw [hω_norm i, inv_one, one_smul]
        have hnorm_state : ‖L.stateAt (ω_c i).1 L.T‖ = 1 := by
          rw [← hψ_eq]; exact hΨ_norm _
        haveI : IsProbabilityMeasure (L.meas (L.stateAt (ω_c i).1 L.T)) := L.meas_povm.1 _ hnorm_state
        rw [hψ_eq, ← hES_eval i _ hnorm_state]
        have h23 := ENNReal.toReal_mono (measure_ne_top _ _) (hS_prob i)
        simpa [ENNReal.toReal_div] using h23
      have habs := (abs_le.mp hdiff_E).1
      linarith
    have hsum_i : ∀ i : Fin M,
        (664 / 1000 : ℝ) * (γ n).real (cone (D i)) ≤
          ∫ g in cone (D i), (∑ σ ∈ Finset.univ.filter (fun σ : Fin M → Bool => σ i = true),
            RCLike.re (inner ℂ (Ψ L L.T g) (E_op σ (Ψ L L.T g)))) ∂(γ n) := by
      intro i
      have hi_sum : IntegrableOn (fun g => ∑ σ ∈ Finset.univ.filter (fun σ : Fin M → Bool => σ i = true),
            RCLike.re (inner ℂ (Ψ L L.T g) (E_op σ (Ψ L L.T g)))) (cone (D i)) (γ n) :=
        integrable_finsetSum _ fun σ _ => (hf_int σ).integrableOn
      have hc_int : IntegrableOn (fun _ : E n => (664 / 1000 : ℝ)) (cone (D i)) (γ n) :=
        integrableOn_const (measure_ne_top _ _)
      have hmono := setIntegral_mono_on_ae hc_int hi_sum (hcone_D_meas i) (hpt_i i)
      simpa [setIntegral_const, smul_eq_mul, mul_comm] using hmono
    have hsum_total : (664 / 1000 : ℝ) * (γ n).real (accCone M) ≤
        ∑ i : Fin M, ∫ g in cone (D i),
          (∑ σ ∈ Finset.univ.filter (fun σ : Fin M → Bool => σ i = true),
            RCLike.re (inner ℂ (Ψ L L.T g) (E_op σ (Ψ L L.T g)))) ∂(γ n) := by
      have hmeas_sum : (γ n).real (accCone M) = ∑ i : Fin M, (γ n).real (cone (D i)) := by
        rw [← hcone_D_union, Measure.real, measure_iUnion hcone_D_disj hcone_D_meas,
          tsum_fintype, ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
        rfl
      rw [hmeas_sum, Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => hsum_i i
    linarith [hM_real]
  refine ⟨M, E_op, Good, hE_pos, hE_le, hE_sum_eq, hGood_meas, hlower, fun σ => ?_⟩
  have hconc0 := H_deg_concentration hn d (E_op σ) (hE_pos σ) v (hU_meas σ)
  refine ⟨hconc0.1, ?_⟩
  have hR_nn : 0 ≤ ∫ g : E n, RCLike.re (inner ℂ (L_deg g) (E_op σ (L_deg g))) ∂(γ n) :=
    integral_nonneg fun g => (hE_pos σ).re_inner_nonneg_right _
  have hcap_nn : 0 ≤ (Module.finrank ℝ (V_d n d) : ℝ) * (6 * Real.pi * ε) ^ (n - 1) := by
    positivity
  by_cases hi : ∃ i₀ : Fin M, σ i₀ = true
  · obtain ⟨i₀, hi₀⟩ := hi
    by_cases ho : ∃ o₀ : L.O, o₀ ∈ A σ
    · obtain ⟨o₀, ho₀⟩ := ho
      let u₀ : Metric.sphere (0 : E n) 1 := ω_c i₀
      let θ : ℝ := 3 * Real.pi * ε
      have hθ_pos : 0 < θ := by positivity
      have hθ_le : θ ≤ Real.pi / 2 := by
        have hpi : 0 < Real.pi := Real.pi_pos
        nlinarith [hpi, hε_le]
      let Cap : Set (Metric.sphere (0 : E n) 1) :=
        {u | Real.cos θ ≤ inner ℝ u.1 u₀.1}
      have hCap_meas : MeasurableSet Cap :=
        measurableSet_le measurable_const ((continuous_subtype_val.inner continuous_const).measurable)
      have hU_sub_Cap : U_cov σ ⊆ Cap := by
        intro u hu
        rw [Set.mem_iUnion₂] at hu
        rcases hu with ⟨i, hi_mem, huB⟩
        have hσi : σ i = true := (Finset.mem_filter.mp hi_mem).2
        have ho_Si : o₀ ∈ S_meas i := by
          have := Set.mem_iInter.mp ho₀ i
          simpa [hσi] using this
        have ho_Si₀ : o₀ ∈ S_meas i₀ := by
          have := Set.mem_iInter.mp ho₀ i₀
          simpa [hi₀] using this
        have hd_o_i : disagree (L.hyp o₀) (ltf (ω_c i).1 0) ≤ ε := hS_sub i ho_Si
        have hd_o_i₀ : disagree (L.hyp o₀) (ltf u₀.1 0) ≤ ε := hS_sub i₀ ho_Si₀
        have hu_norm : ‖u.1‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
        have hl1 := (QuantumLTF.Membership.lemma_2_1 u.1 (ω_c i).1 hu_norm (hω_norm i) 0 0).1
        have hdist_u : ‖u.1 - (ω_c i).1‖ < 2 * ε :=
          lt_of_lt_of_le (hB_prop i u huB) (hδ_le (seq i.1).1)
        have hd_u_i : disagree (ltf u.1 0) (ltf (ω_c i).1 0) ≤ ε := by
          have h0 : |0 - 0| / Real.sqrt (2 * Real.pi) = 0 := by simp
          rw [h0, add_zero] at hl1
          linarith
        have hd_u_u₀ : disagree (ltf u.1 0) (ltf u₀.1 0) ≤ 3 * ε := by
          have ht1 := disagree_triangle (ltf u.1 0) (ltf (ω_c i).1 0) (ltf u₀.1 0)
          have ht2 := disagree_triangle (ltf (ω_c i).1 0) (L.hyp o₀) (ltf u₀.1 0)
          rw [disagree_symm (ltf (ω_c i).1 0) (L.hyp o₀)] at ht2
          linarith
        have hl2 := (QuantumLTF.Membership.lemma_2_1 u.1 u₀.1 hu_norm (hω_norm i₀) 0 0).2
        rw [hl2] at hd_u_u₀
        have harc_le : Real.arccos (inner ℝ u.1 u₀.1) ≤ θ := by
          have hmul := mul_le_mul_of_nonneg_left hd_u_u₀ Real.pi_pos.le
          have hdiv : Real.pi * (Real.arccos (inner ℝ u.1 u₀.1) / Real.pi) =
              Real.arccos (inner ℝ u.1 u₀.1) := mul_div_cancel₀ _ Real.pi_pos.ne'
          rw [hdiv] at hmul
          linarith
        have hin_abs : |inner ℝ u.1 u₀.1| ≤ 1 := by
          calc |inner ℝ u.1 u₀.1| ≤ ‖u.1‖ * ‖u₀.1‖ := abs_real_inner_le_norm u.1 u₀.1
            _ = 1 := by rw [hu_norm, hω_norm i₀, mul_one]
        have hin_bdd := abs_le.mp hin_abs
        have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (Real.arccos_nonneg _)
          (hθ_le.trans (by linarith [Real.pi_pos])) harc_le
        rwa [Real.cos_arccos hin_bdd.1 hin_bdd.2] at hcos
      have hGood_sub : Good σ ⊆ cone Cap := by
        intro g hg
        rcases hg with ⟨hg0, u, hu, hgu⟩
        exact ⟨hg0, u, hU_sub_Cap hu, hgu⟩
      have hconc_cap := H_deg_concentration hn d (E_op σ) (hE_pos σ) v hCap_meas
      have hmono : ∫ g in Good σ, RCLike.re (inner ℂ (L_deg g) (E_op σ (L_deg g))) ∂(γ n) ≤
          ∫ g in cone Cap, RCLike.re (inner ℂ (L_deg g) (E_op σ (L_deg g))) ∂(γ n) :=
        setIntegral_mono_set hconc_cap.1.integrableOn
          (ae_of_all _ fun g => (hE_pos σ).re_inner_nonneg_right _)
          (Eventually.of_forall hGood_sub)
      have hcap_bound := μS_cap_le hn u₀ hθ_pos hθ_le
      have h2theta : 2 * θ = 6 * Real.pi * ε := by dsimp [θ]; ring
      rw [h2theta] at hcap_bound
      calc ∫ g in Good σ, RCLike.re (inner ℂ (L_deg g) (E_op σ (L_deg g))) ∂(γ n)
          ≤ ∫ g in cone Cap, RCLike.re (inner ℂ (L_deg g) (E_op σ (L_deg g))) ∂(γ n) := hmono
        _ ≤ (Module.finrank ℝ (V_d n d) : ℝ) * (μS n).real Cap *
              ∫ g : E n, RCLike.re (inner ℂ (L_deg g) (E_op σ (L_deg g))) ∂(γ n) := hconc_cap.2
        _ ≤ (Module.finrank ℝ (V_d n d) : ℝ) * (6 * Real.pi * ε) ^ (n - 1) *
              ∫ g : E n, RCLike.re (inner ℂ (L_deg g) (E_op σ (L_deg g))) ∂(γ n) := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcap_bound (Nat.cast_nonneg _)) hR_nn
    · have hA_empty : A σ = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro o hoA; exact ho ⟨o, hoA⟩
      have hE_zero : ∀ x : lp (fun _ : (E n × Bool) × L.Ω => ℂ) 2,
          RCLike.re (inner ℂ x (E_op σ x)) = 0 := by
        intro x
        by_cases hx0 : x = 0
        · simp [hx0]
        · let u : lp (fun _ : (E n × Bool) × L.Ω => ℂ) 2 := ‖x‖⁻¹ • x
          have hu : ‖u‖ = 1 := norm_smul_inv_norm hx0
          have hu0 : RCLike.re (inner ℂ u (E_op σ u)) = 0 := by
            rw [← hE_eval σ u hu, hA_empty, measure_empty, ENNReal.toReal_zero]
          rw [pos_op_scale (E_op σ) x hx0]
          exact mul_eq_zero.mpr (Or.inr hu0)
      simp_rw [hE_zero]
      simp
  · have hU_empty : U_cov σ = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro u hu
      rw [Set.mem_iUnion₂] at hu
      rcases hu with ⟨i, hi_mem, _⟩
      exact hi ⟨i, (Finset.mem_filter.mp hi_mem).2⟩
    have hGood_empty : Good σ = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro g hg
      rcases hg with ⟨_, u, hu, _⟩
      rw [hU_empty] at hu
      exact hu
    rw [hGood_empty, setIntegral_empty]
    exact mul_nonneg hcap_nn hR_nn

end LearnerBound

end LearnerModule


end Aux_w_mq_lb

open QuantumLTF.Membership QuantumLTF.Membership.Supplement

theorem solution :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ ε0 →
        ∀ L : QMemLearner n,
          (∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 → L.Succeeds w ε) →
            c * Real.log (n / ε) ≤ L.T := by
  let c₀ : ℝ := 1 / (384 * Real.pi * Real.exp 1)
  have hc₀_pos : 0 < c₀ := by positivity
  have hc₀_lt1 : c₀ < 1 := by
    have hpi : 3 < Real.pi := Real.pi_gt_three
    have hexp : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr one_pos
    have hden : (1 : ℝ) < 384 * Real.pi * Real.exp 1 := by nlinarith
    exact (div_lt_one (by positivity)).mpr hden
  let K0 : ℝ := 4 * (2 / c₀) ^ (1 / 4 : ℝ)
  have hK0_pos : 0 < K0 := by positivity
  let ε0 : ℝ := min (c₀ / 100) (K0 ^ (-8 : ℝ))
  have hε0_pos : 0 < ε0 := lt_min (by positivity) (by positivity)
  let c : ℝ := 1 / (8 * Real.log 4402)
  have hlog4402_pos : 0 < Real.log 4402 := Real.log_pos (by norm_num)
  have hc_pos : 0 < c := by positivity
  refine ⟨ε0, hε0_pos, c, hc_pos, ?_⟩
  intro n hn ε hε_pos hε_le L hsucc
  have hε_le_c0 : ε ≤ c₀ / 100 := hε_le.trans (min_le_left _ _)
  have hε_le_K0 : ε ≤ K0 ^ (-8 : ℝ) := hε_le.trans (min_le_right _ _)
  have hε3_le : 3 * ε ≤ 1 / 2 := by linarith
  let d : ℕ := ⌊c₀ * (n - 1 : ℝ) / ε⌋₊
  have hn1_pos : (0 : ℝ) < (n - 1 : ℝ) := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hn2_le : (n : ℝ) / 2 ≤ (n - 1 : ℝ) := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  -- 1. Degree-`d` concentration factor ≤ 1 / 16
  have hcap_factor_le :
      (Module.finrank ℝ (Aux_w_mq_lb.V_d n d) : ℝ) * (6 * Real.pi * ε) ^ (n - 1) ≤ 1 / 16 := by
    have hfin := Aux_w_mq_lb.finrank_V_d_le hn d
    have hd_le : (d : ℝ) ≤ c₀ * (n - 1 : ℝ) / ε := Nat.floor_le (by positivity)
    have hd_div : (d : ℝ) / (n - 1 : ℝ) ≤ c₀ / ε := by
      rw [div_le_iff₀ hn1_pos]
      calc (d : ℝ) ≤ c₀ * (n - 1 : ℝ) / ε := hd_le
        _ = (c₀ / ε) * (n - 1 : ℝ) := by ring
    have hbase_le : Real.exp 1 * (1 + (d : ℝ) / (n - 1 : ℝ)) * (6 * Real.pi * ε) ≤ 1 / 32 := by
      have h1 : Real.exp 1 * (1 + (d : ℝ) / (n - 1 : ℝ)) * (6 * Real.pi * ε) ≤
          Real.exp 1 * (1 + c₀ / ε) * (6 * Real.pi * ε) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (by positivity)
      have h2 : Real.exp 1 * (1 + c₀ / ε) * (6 * Real.pi * ε) =
          6 * Real.pi * Real.exp 1 * (ε + c₀) := by
        field_simp [hε_pos.ne']
      have h3 : 6 * Real.pi * Real.exp 1 * (ε + c₀) ≤
          6 * Real.pi * Real.exp 1 * ((101 / 100 : ℝ) * c₀) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h4 : 6 * Real.pi * Real.exp 1 * ((101 / 100 : ℝ) * c₀) = 101 / 6400 := by
        dsimp [c₀]
        have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
        have hexp0 : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
        field_simp [hpi0, hexp0]
        norm_num
      linarith
    have hbase_nn : 0 ≤ Real.exp 1 * (1 + (d : ℝ) / (n - 1 : ℝ)) * (6 * Real.pi * ε) := by
      have : 0 ≤ (d : ℝ) / (n - 1 : ℝ) := by positivity
      positivity
    have hpow_le :
        (Real.exp 1 * (1 + (d : ℝ) / (n - 1 : ℝ))) ^ (n - 1) * (6 * Real.pi * ε) ^ (n - 1) ≤
          1 / 32 := by
      rw [← mul_pow]
      have hn1_ge : 1 ≤ n - 1 := by omega
      calc (Real.exp 1 * (1 + (d : ℝ) / (n - 1 : ℝ)) * (6 * Real.pi * ε)) ^ (n - 1)
          ≤ (1 / 32 : ℝ) ^ (n - 1) := pow_le_pow_left₀ hbase_nn hbase_le (n - 1)
        _ ≤ (1 / 32 : ℝ) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn1_ge
        _ = 1 / 32 := pow_one _
    calc (Module.finrank ℝ (Aux_w_mq_lb.V_d n d) : ℝ) * (6 * Real.pi * ε) ^ (n - 1)
        ≤ (2 * (Real.exp 1 * (1 + (d : ℝ) / (n - 1 : ℝ))) ^ (n - 1)) * (6 * Real.pi * ε) ^ (n - 1) :=
          mul_le_mul_of_nonneg_right hfin (by positivity)
      _ = 2 * ((Real.exp 1 * (1 + (d : ℝ) / (n - 1 : ℝ))) ^ (n - 1) * (6 * Real.pi * ε) ^ (n - 1)) := by
          ring
      _ ≤ 2 * (1 / 32) := mul_le_mul_of_nonneg_left hpow_le (by norm_num)
      _ = 1 / 16 := by norm_num
  -- 2. Split Ψ = L_deg + H_rem and combine POVM lower bound with low-degree cap bound
  let v : (Fin n → ℕ) → lp (fun _ : (Aux_w_mq_lb.E n × Bool) × L.Ω => ℂ) 2 :=
    fun α => ∫ g : Aux_w_mq_lb.E n, (Aux_w_mq_lb.Hnd α g : ℂ) • Aux_w_mq_lb.Ψ L L.T g ∂(Aux_w_mq_lb.γ n)
  let L_deg : Aux_w_mq_lb.E n → lp (fun _ : (Aux_w_mq_lb.E n × Bool) × L.Ω => ℂ) 2 :=
    fun g => ∑ α ∈ Aux_w_mq_lb.I_deg n d, (Aux_w_mq_lb.Hnd α g : ℂ) • v α
  let H_rem : Aux_w_mq_lb.E n → lp (fun _ : (Aux_w_mq_lb.E n × Bool) × L.Ω => ℂ) 2 :=
    fun g => Aux_w_mq_lb.Ψ L L.T g - L_deg g
  rcases Aux_w_mq_lb.H_parseval_tail_le hn L d with ⟨hL_sq_int, hL_int_le, hrem_sq_int, htail_W⟩
  obtain ⟨M, E_op, Good, hE_pos, hE_le, hE_sum_eq, hGood_meas, hlower, hconc⟩ :=
    Aux_w_mq_lb.learner_cover_and_povm hn L hε_pos hε3_le hsucc d
  have hΨ_meas : AEStronglyMeasurable (Aux_w_mq_lb.Ψ L L.T) (Aux_w_mq_lb.γ n) :=
    Aux_w_mq_lb.aestronglyMeasurable_Ψ hn L L.T le_rfl
  have hΨ_norm : ∀ g, ‖Aux_w_mq_lb.Ψ L L.T g‖ = 1 := Aux_w_mq_lb.Ψ_norm L L.T
  have hL_cont : Continuous L_deg := by
    refine continuous_finsetSum _ fun α _ => ?_
    exact (Complex.continuous_ofReal.comp (Aux_w_mq_lb.continuous_Hnd α)).smul continuous_const
  have hrem_meas : AEStronglyMeasurable H_rem (Aux_w_mq_lb.γ n) :=
    hΨ_meas.sub hL_cont.aestronglyMeasurable
  have hf_int : ∀ σ : Fin M → Bool,
      Integrable (fun g => RCLike.re (inner ℂ (Aux_w_mq_lb.Ψ L L.T g) (E_op σ (Aux_w_mq_lb.Ψ L L.T g))))
        (Aux_w_mq_lb.γ n) := by
    intro σ
    have hsm := Complex.continuous_re.comp_aestronglyMeasurable
      (hΨ_meas.inner ((E_op σ).continuous.comp_aestronglyMeasurable hΨ_meas))
    refine Integrable.of_bound hsm 1 (ae_of_all _ fun g => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg ((hE_pos σ).re_inner_nonneg_right _)]
    exact (hE_le σ (Aux_w_mq_lb.Ψ L L.T g)).trans_eq (by rw [hΨ_norm g, one_pow])
  have hrem_int : ∀ σ : Fin M → Bool,
      Integrable (fun g => RCLike.re (inner ℂ (H_rem g) (E_op σ (H_rem g)))) (Aux_w_mq_lb.γ n) := by
    intro σ
    have hsm := Complex.continuous_re.comp_aestronglyMeasurable
      (hrem_meas.inner ((E_op σ).continuous.comp_aestronglyMeasurable hrem_meas))
    refine hrem_sq_int.mono' hsm (ae_of_all _ fun g => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg ((hE_pos σ).re_inner_nonneg_right _)]
    exact hE_le σ (H_rem g)
  have hamgm : ∀ {u a b : ℝ}, 0 ≤ a → 0 ≤ b → u ^ 2 ≤ a * b → u ≤ a + (1 / 4 : ℝ) * b := by
    intro u a b ha hb hsq
    by_contra hlt
    push Not at hlt
    have hpos : 0 < u + (a + (1 / 4 : ℝ) * b) := by linarith
    have hmul : 0 < (u - (a + (1 / 4 : ℝ) * b)) * (u + (a + (1 / 4 : ℝ) * b)) :=
      mul_pos (sub_pos.mpr hlt) hpos
    nlinarith [sq_nonneg (a - (1 / 4 : ℝ) * b)]
  have hpt_amgm : ∀ (σ : Fin M → Bool) (g : Aux_w_mq_lb.E n),
      RCLike.re (inner ℂ (Aux_w_mq_lb.Ψ L L.T g) (E_op σ (Aux_w_mq_lb.Ψ L L.T g))) ≤
        3 * RCLike.re (inner ℂ (L_deg g) (E_op σ (L_deg g))) +
          (3 / 2 : ℝ) * RCLike.re (inner ℂ (H_rem g) (E_op σ (H_rem g))) := by
    intro σ g
    have hsplit : Aux_w_mq_lb.Ψ L L.T g = L_deg g + H_rem g := (add_sub_cancel _ _).symm
    rw [hsplit, map_add, inner_add_left, inner_add_right, inner_add_right]
    simp only [Aux_w_mq_lb.rclike_re_eq, Complex.add_re]
    have ha : 0 ≤ RCLike.re (inner ℂ (L_deg g) (E_op σ (L_deg g))) :=
      (hE_pos σ).re_inner_nonneg_right _
    have hb : 0 ≤ RCLike.re (inner ℂ (H_rem g) (E_op σ (H_rem g))) :=
      (hE_pos σ).re_inner_nonneg_right _
    have h1 := hamgm ha hb (Aux_w_mq_lb.re_inner_pos_op_le (hE_pos σ) (L_deg g) (H_rem g))
    have hcs2 := Aux_w_mq_lb.re_inner_pos_op_le (hE_pos σ) (H_rem g) (L_deg g)
    rw [mul_comm] at hcs2
    have h2 := hamgm ha hb hcs2
    simp only [Aux_w_mq_lb.rclike_re_eq] at ha hb h1 h2
    linarith
  have hgood_sum_le :
      (∑ σ : Fin M → Bool,
          ∫ g in Good σ, RCLike.re (inner ℂ (Aux_w_mq_lb.Ψ L L.T g) (E_op σ (Aux_w_mq_lb.Ψ L L.T g)))
            ∂(Aux_w_mq_lb.γ n)) ≤
        3 * (1 / 16 : ℝ) *
            (∑ σ : Fin M → Bool,
              ∫ g : Aux_w_mq_lb.E n, RCLike.re (inner ℂ (L_deg g) (E_op σ (L_deg g))) ∂(Aux_w_mq_lb.γ n)) +
          (3 / 2 : ℝ) *
            (∑ σ : Fin M → Bool,
              ∫ g : Aux_w_mq_lb.E n, RCLike.re (inner ℂ (H_rem g) (E_op σ (H_rem g))) ∂(Aux_w_mq_lb.γ n)) := by
    have hper : ∀ σ : Fin M → Bool,
        ∫ g in Good σ, RCLike.re (inner ℂ (Aux_w_mq_lb.Ψ L L.T g) (E_op σ (Aux_w_mq_lb.Ψ L L.T g)))
            ∂(Aux_w_mq_lb.γ n) ≤
          3 * ((1 / 16 : ℝ) *
              ∫ g : Aux_w_mq_lb.E n, RCLike.re (inner ℂ (L_deg g) (E_op σ (L_deg g))) ∂(Aux_w_mq_lb.γ n)) +
            (3 / 2 : ℝ) *
              ∫ g : Aux_w_mq_lb.E n, RCLike.re (inner ℂ (H_rem g) (E_op σ (H_rem g))) ∂(Aux_w_mq_lb.γ n) := by
      intro σ
      have hint_L : IntegrableOn (fun g => RCLike.re (inner ℂ (L_deg g) (E_op σ (L_deg g))))
          (Good σ) (Aux_w_mq_lb.γ n) := (hconc σ).1.integrableOn
      have hint_R : IntegrableOn (fun g => RCLike.re (inner ℂ (H_rem g) (E_op σ (H_rem g))))
          (Good σ) (Aux_w_mq_lb.γ n) := (hrem_int σ).integrableOn
      have hrhs_int : IntegrableOn
          (fun g => 3 * RCLike.re (inner ℂ (L_deg g) (E_op σ (L_deg g))) +
            (3 / 2 : ℝ) * RCLike.re (inner ℂ (H_rem g) (E_op σ (H_rem g))))
          (Good σ) (Aux_w_mq_lb.γ n) :=
        (hint_L.const_mul 3).add (hint_R.const_mul (3 / 2))
      have hmono := setIntegral_mono_on (hf_int σ).integrableOn hrhs_int (hGood_meas σ)
        (fun g _ => hpt_amgm σ g)
      rw [integral_add (hint_L.const_mul 3) (hint_R.const_mul (3 / 2)),
        integral_const_mul, integral_const_mul] at hmono
      have hL_full : 0 ≤ ∫ g : Aux_w_mq_lb.E n,
          RCLike.re (inner ℂ (L_deg g) (E_op σ (L_deg g))) ∂(Aux_w_mq_lb.γ n) :=
        integral_nonneg fun g => (hE_pos σ).re_inner_nonneg_right _
      have hL_good_le :
          ∫ g in Good σ, RCLike.re (inner ℂ (L_deg g) (E_op σ (L_deg g))) ∂(Aux_w_mq_lb.γ n) ≤
            (1 / 16 : ℝ) *
              ∫ g : Aux_w_mq_lb.E n, RCLike.re (inner ℂ (L_deg g) (E_op σ (L_deg g))) ∂(Aux_w_mq_lb.γ n) :=
        (hconc σ).2.trans (mul_le_mul_of_nonneg_right hcap_factor_le hL_full)
      have hR_good_le :
          ∫ g in Good σ, RCLike.re (inner ℂ (H_rem g) (E_op σ (H_rem g))) ∂(Aux_w_mq_lb.γ n) ≤
            ∫ g : Aux_w_mq_lb.E n, RCLike.re (inner ℂ (H_rem g) (E_op σ (H_rem g))) ∂(Aux_w_mq_lb.γ n) :=
        setIntegral_le_integral (hrem_int σ) (ae_of_all _ fun g => (hE_pos σ).re_inner_nonneg_right _)
      linarith
    calc (∑ σ : Fin M → Bool,
            ∫ g in Good σ, RCLike.re (inner ℂ (Aux_w_mq_lb.Ψ L L.T g) (E_op σ (Aux_w_mq_lb.Ψ L L.T g)))
              ∂(Aux_w_mq_lb.γ n))
        ≤ ∑ σ : Fin M → Bool,
            (3 * ((1 / 16 : ℝ) *
                ∫ g : Aux_w_mq_lb.E n, RCLike.re (inner ℂ (L_deg g) (E_op σ (L_deg g))) ∂(Aux_w_mq_lb.γ n)) +
              (3 / 2 : ℝ) *
                ∫ g : Aux_w_mq_lb.E n, RCLike.re (inner ℂ (H_rem g) (E_op σ (H_rem g))) ∂(Aux_w_mq_lb.γ n)) :=
          Finset.sum_le_sum fun σ _ => hper σ
      _ = 3 * (1 / 16 : ℝ) *
            (∑ σ : Fin M → Bool,
              ∫ g : Aux_w_mq_lb.E n, RCLike.re (inner ℂ (L_deg g) (E_op σ (L_deg g))) ∂(Aux_w_mq_lb.γ n)) +
          (3 / 2 : ℝ) *
            (∑ σ : Fin M → Bool,
              ∫ g : Aux_w_mq_lb.E n, RCLike.re (inner ℂ (H_rem g) (E_op σ (H_rem g))) ∂(Aux_w_mq_lb.γ n)) := by
          rw [Finset.sum_add_distrib]
          simp only [← Finset.mul_sum, mul_assoc]
  have hsum_L_eq :
      (∑ σ : Fin M → Bool,
          ∫ g : Aux_w_mq_lb.E n, RCLike.re (inner ℂ (L_deg g) (E_op σ (L_deg g))) ∂(Aux_w_mq_lb.γ n)) =
        ∫ g : Aux_w_mq_lb.E n, ‖L_deg g‖ ^ 2 ∂(Aux_w_mq_lb.γ n) := by
    rw [← integral_finsetSum _ fun σ _ => (hconc σ).1]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    exact hE_sum_eq (L_deg g)
  have hsum_rem_eq :
      (∑ σ : Fin M → Bool,
          ∫ g : Aux_w_mq_lb.E n, RCLike.re (inner ℂ (H_rem g) (E_op σ (H_rem g))) ∂(Aux_w_mq_lb.γ n)) =
        ∫ g : Aux_w_mq_lb.E n, ‖H_rem g‖ ^ 2 ∂(Aux_w_mq_lb.γ n) := by
    rw [← integral_finsetSum _ fun σ _ => hrem_int σ]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    exact hE_sum_eq (H_rem g)
  rw [hsum_L_eq, hsum_rem_eq] at hgood_sum_le
  have hrem_gt : (1 / 4 : ℝ) < ∫ g : Aux_w_mq_lb.E n, ‖H_rem g‖ ^ 2 ∂(Aux_w_mq_lb.γ n) := by
    have : (64 / 100 : ℝ) < 3 * (1 / 16 : ℝ) * 1 + (3 / 2 : ℝ) *
        ∫ g : Aux_w_mq_lb.E n, ‖H_rem g‖ ^ 2 ∂(Aux_w_mq_lb.γ n) := by
      have hm : 3 * (1 / 16 : ℝ) * ∫ g : Aux_w_mq_lb.E n, ‖L_deg g‖ ^ 2 ∂(Aux_w_mq_lb.γ n) ≤
          3 * (1 / 16 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hL_int_le (by norm_num)
      linarith
    linarith
  -- 3. Combine tail weight lower bound with inductive W_H upper bound
  have hW_tot : ENNReal.ofReal ((d + 2 : ℝ) ^ (1 / 4 : ℝ) *
      ∫ g : Aux_w_mq_lb.E n, ‖H_rem g‖ ^ 2 ∂(Aux_w_mq_lb.γ n)) ≤ (4402 : ℝ≥0∞) ^ L.T :=
    htail_W.trans (Aux_w_mq_lb.W_H_Ψ_le hn L L.T le_rfl)
  have h4402_eq : (4402 : ℝ≥0∞) ^ L.T = ENNReal.ofReal ((4402 : ℝ) ^ L.T) := by
    rw [ENNReal.ofReal_pow (by norm_num)]
    congr 1
    norm_num
  rw [h4402_eq, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hW_tot
  have hd_pow_le : (1 / 4 : ℝ) * (d + 2 : ℝ) ^ (1 / 4 : ℝ) ≤ (4402 : ℝ) ^ L.T := by
    have h1 : (1 / 4 : ℝ) * (d + 2 : ℝ) ^ (1 / 4 : ℝ) ≤
        (d + 2 : ℝ) ^ (1 / 4 : ℝ) * ∫ g : Aux_w_mq_lb.E n, ‖H_rem g‖ ^ 2 ∂(Aux_w_mq_lb.γ n) := by
      rw [mul_comm (1 / 4 : ℝ)]
      exact mul_le_mul_of_nonneg_left hrem_gt.le (by positivity)
    exact h1.trans hW_tot
  -- 4. Convert (d + 2)^{1/4} into (n / ε)^{1/8} and take logarithms
  let X : ℝ := (n : ℝ) / ε
  have hX_pos : 0 < X := by positivity
  have hc₀2_X_le : (c₀ / 2) * X ≤ (d : ℝ) + 2 := by
    have hlt : c₀ * (n - 1 : ℝ) / ε < (d : ℝ) + 1 := Nat.lt_floor_add_one _
    have hm : c₀ * ((n : ℝ) / 2) ≤ c₀ * (n - 1 : ℝ) :=
      mul_le_mul_of_nonneg_left hn2_le hc₀_pos.le
    have hdiv : c₀ * ((n : ℝ) / 2) / ε ≤ c₀ * (n - 1 : ℝ) / ε :=
      div_le_div_of_nonneg_right hm hε_pos.le
    have heq : (c₀ / 2) * X = c₀ * ((n : ℝ) / 2) / ε :=
      show (c₀ / 2) * ((n : ℝ) / ε) = c₀ * ((n : ℝ) / 2) / ε by ring
    linarith
  have hK0_le_X18 : K0 ≤ X ^ (1 / 8 : ℝ) := by
    have hinv_le : K0 ^ (8 : ℝ) ≤ ε⁻¹ := by
      have h1 : (K0 ^ (-8 : ℝ))⁻¹ ≤ ε⁻¹ := inv_anti₀ hε_pos hε_le_K0
      have h2 : (K0 ^ (-8 : ℝ))⁻¹ = K0 ^ (8 : ℝ) := by
        rw [Real.rpow_neg hK0_pos.le, inv_inv]
      rwa [h2] at h1
    have hn_ge1 : (1 : ℝ) ≤ n := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hK_le_X : K0 ^ (8 : ℝ) ≤ X := by
      have h1 : K0 ^ (8 : ℝ) ≤ 1 * ε⁻¹ := by linarith
      have h2 : (1 : ℝ) * ε⁻¹ ≤ (n : ℝ) * ε⁻¹ := mul_le_mul_of_nonneg_right hn_ge1 (by positivity)
      have h3 : (n : ℝ) * ε⁻¹ = X := (div_eq_mul_inv (n : ℝ) ε).symm
      linarith
    have hpow := Real.rpow_le_rpow (by positivity) hK_le_X (by norm_num : (0 : ℝ) ≤ 1 / 8)
    have hid : (K0 ^ (8 : ℝ)) ^ (1 / 8 : ℝ) = K0 := by
      rw [← Real.rpow_mul hK0_pos.le]
      norm_num
    rwa [hid] at hpow
  have hX18_le : X ^ (1 / 8 : ℝ) ≤ (1 / 4 : ℝ) * ((c₀ / 2) * X) ^ (1 / 4 : ℝ) := by
    have hX14 : X ^ (1 / 4 : ℝ) = X ^ (1 / 8 : ℝ) * X ^ (1 / 8 : ℝ) := by
      rw [← Real.rpow_add hX_pos]
      norm_num
    have hc_inv : (c₀ / 2) ^ (1 / 4 : ℝ) = ((2 / c₀) ^ (1 / 4 : ℝ))⁻¹ := by
      have heq : c₀ / 2 = (2 / c₀)⁻¹ := by field_simp [hc₀_pos.ne']
      rw [heq, Real.inv_rpow (by positivity)]
    have hrhs_eq : (1 / 4 : ℝ) * ((c₀ / 2) * X) ^ (1 / 4 : ℝ) =
        K0⁻¹ * (X ^ (1 / 8 : ℝ) * X ^ (1 / 8 : ℝ)) := by
      rw [Real.mul_rpow (by positivity) hX_pos.le, hc_inv, hX14]
      dsimp [K0]
      rw [mul_inv, one_div]
      ring
    rw [hrhs_eq, ← mul_le_mul_iff_right₀ hK0_pos]
    have h1 : X ^ (1 / 8 : ℝ) * K0 ≤ X ^ (1 / 8 : ℝ) * X ^ (1 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_left hK0_le_X18 (by positivity)
    have h2 : (K0⁻¹ * (X ^ (1 / 8 : ℝ) * X ^ (1 / 8 : ℝ))) * K0 = X ^ (1 / 8 : ℝ) * X ^ (1 / 8 : ℝ) := by
      field_simp [hK0_pos.ne']
    linarith
  have hX18_le_4402 : X ^ (1 / 8 : ℝ) ≤ (4402 : ℝ) ^ L.T := by
    have hstep1 : ((c₀ / 2) * X) ^ (1 / 4 : ℝ) ≤ (d + 2 : ℝ) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hc₀2_X_le (by norm_num)
    have hstep2 : (1 / 4 : ℝ) * ((c₀ / 2) * X) ^ (1 / 4 : ℝ) ≤ (1 / 4 : ℝ) * (d + 2 : ℝ) ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hstep1 (by norm_num)
    linarith
  have hlog_le : Real.log (X ^ (1 / 8 : ℝ)) ≤ Real.log ((4402 : ℝ) ^ L.T) :=
    Real.log_le_log (by positivity) hX18_le_4402
  rw [Real.log_rpow hX_pos, Real.log_pow] at hlog_le
  have hdiv_le : ((1 / 8 : ℝ) * Real.log X) / Real.log 4402 ≤ ((L.T : ℝ) * Real.log 4402) / Real.log 4402 :=
    div_le_div_of_nonneg_right hlog_le hlog4402_pos.le
  have hlhs_eq : c * Real.log (n / ε) = ((1 / 8 : ℝ) * Real.log X) / Real.log 4402 := by
    dsimp [c, X]
    ring
  have hrhs_eq : ((L.T : ℝ) * Real.log 4402) / Real.log 4402 = L.T := by
    field_simp [hlog4402_pos.ne']
  linarith
