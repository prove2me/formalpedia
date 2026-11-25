-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.band_channel_algebra_54
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-25T01:13:43.031434+00:00
-- url     : https://prove2.me/submissions/9f99a8ee-5c86-4f0a-b211-832ac7939d4d

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_padKet
import Definitions.Def_QuantumLTF_Membership_Supplement_dirAmp
import Definitions.Def_QuantumLTF_Membership_Supplement_dirTensorPow
import Definitions.Def_QuantumLTF_Membership_Supplement_measChannelOut
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Theorems.Thm_QuantumLTF_Membership_Supplement_hermite_band_bounds_53

set_option autoImplicit false

namespace Aux_hermite_54

open MeasureTheory Filter Polynomial QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open scoped Real Topology Nat ENNReal

/-! ### Part 1: 1D Gaussian Density & Orthonormal Hermite Functions -/

noncomputable def phi (x : ℝ) : ℝ := ProbabilityTheory.gaussianPDFReal 0 1 x

lemma phi_def (x : ℝ) : phi x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)) := by
  simp [phi, ProbabilityTheory.gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one, neg_div]

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
  | zero => simp [Hpoly, Polynomial.hermite_zero]
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

noncomputable def h1D (j : ℕ) (x : ℝ) : ℝ :=
  (Real.sqrt (j.factorial : ℝ))⁻¹ * Hpoly j x

lemma h1D_eq_div (j : ℕ) (x : ℝ) :
    h1D j x = Polynomial.aeval x (Polynomial.hermite j) / Real.sqrt (j.factorial) := by
  simp [h1D, Hpoly, div_eq_inv_mul]

lemma continuous_h1D (j : ℕ) : Continuous (h1D j) := by
  have : h1D j = fun x =>
      (Real.sqrt (j.factorial : ℝ))⁻¹ * ((Polynomial.hermite j).map (algebraMap ℤ ℝ)).eval x := by
    ext x; simp [h1D, Hpoly, Polynomial.aeval_def, Polynomial.eval_map]
  rw [this]
  fun_prop

lemma h1D_zero_fn (x : ℝ) : h1D 0 x = 1 := by
  simp [h1D, Hpoly]

noncomputable def h1D_deriv (j : ℕ) (x : ℝ) : ℝ :=
  if j = 0 then 0 else Real.sqrt (j : ℝ) * h1D (j - 1) x

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
      rw [show (((k + 1 + 1 : ℕ) : ℝ)) = k + 2 by push_cast; ring, mul_comm]
    have hfac2 : (Real.sqrt ((k + 1).factorial : ℝ))⁻¹ =
        (Real.sqrt (k + 1 : ℝ))⁻¹ * (Real.sqrt (k.factorial : ℝ))⁻¹ := by
      rw [Nat.factorial_succ k, Nat.cast_mul, Real.sqrt_mul (by positivity), mul_inv]
      rw [show (((k + 1 : ℕ) : ℝ)) = k + 1 by push_cast; ring, mul_comm]
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
      have hsq : |x| ^ (2 * k) = x ^ (2 * k) := by rw [pow_mul, sq_abs, ← pow_mul]
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
          rw [show (((m + 1 : ℕ) : ℝ)) = m + 1 by push_cast; ring, mul_comm]
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

lemma h1D_orthonormal (j k : ℕ) :
    ∫ x : ℝ, h1D j x * h1D k x ∂(ProbabilityTheory.gaussianReal 0 1) =
      if j = k then 1 else 0 := by
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul one_ne_zero]
  have heq : (fun x : ℝ => ProbabilityTheory.gaussianPDFReal 0 1 x • (h1D j x * h1D k x)) =
      fun x => h1D j x * h1D k x * phi x := by
    ext x; simp [phi, smul_eq_mul]; ring
  rw [heq]
  exact h1D_orthonormal_aux j k

noncomputable def coeff1D (k : ℕ) : ℝ :=
  ∫ x : ℝ, (sgn x : ℝ) * h1D k x ∂(ProbabilityTheory.gaussianReal 0 1)

/-! ### Part 2: Multivariate Hermite Polynomials & Orthonormal Rotations -/

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def γ (n : ℕ) : Measure (E n) := ProbabilityTheory.stdGaussian (E n)

instance isProbabilityMeasure_γ (n : ℕ) : IsProbabilityMeasure (γ n) := by
  unfold γ
  infer_instance

noncomputable def Hnd {n : ℕ} (α : Fin n → ℕ) (g : E n) : ℝ :=
  ∏ i : Fin n, h1D (α i) (g i)

@[fun_prop]
lemma continuous_Hnd {n : ℕ} (α : Fin n → ℕ) : Continuous (Hnd α) := by
  unfold Hnd
  refine continuous_finsetProd _ fun i _ => ?_
  exact (continuous_h1D (α i)).comp (PiLp.continuous_apply 2 (fun _ => ℝ) i)

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

lemma integrable_mul_of_memLp_two {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {u v : Ω → ℝ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    Integrable (fun x => u x * v x) μ := by
  refine ((hu.integrable_sq.add hv.integrable_sq).div_const 2).mono' (hu.1.mul hv.1)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs]
  dsimp only [Pi.add_apply]
  nlinarith [abs_nonneg (u x), abs_nonneg (v x), abs_mul (u x) (v x),
    sq_abs (u x), sq_abs (v x), sq_nonneg (|u x| - |v x|)]

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
  | zero => simp [h1D]
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
  | zero => simpa using hf
  | succ k ih =>
    have heq : (fun g : E n => (inner ℝ g u) ^ (k + 1) * f g) =
        fun g => inner ℝ g u * ((inner ℝ g u) ^ k * f g) := by ext g; ring
    rw [heq, ← add_assoc]
    exact mul_inner_mem_P_Hnd (ih hf) u

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
    | empty => simpa using one_mem_P_Hnd n
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

noncomputable def coeff_nd {n : ℕ} (f : E n → ℝ) (α : Fin n → ℕ) : ℝ :=
  ∫ g : E n, Hnd α g * f g ∂(γ n)

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

lemma measurePreserving_isom_γ {n : ℕ} (R : E n ≃ₗᵢ[ℝ] E n) :
    MeasurePreserving R (γ n) (γ n) :=
  ⟨R.continuous.measurable, ProbabilityTheory.stdGaussian_map R⟩

noncomputable def householderReal {n : ℕ} (v : E n) (hv : v ≠ 0) : E n ≃ₗᵢ[ℝ] E n :=
  let c : ℝ := 2 / ‖v‖ ^ 2
  let map : E n →ₗ[ℝ] E n :=
    { toFun := fun x => x - (c * inner ℝ v x) • v
      map_add' := fun x y => by simp [inner_add_right, mul_add, add_smul]; abel
      map_smul' := fun r x => by
        simp only [inner_smul_right, smul_sub, smul_smul, RingHom.id_apply]
        congr 1; congr 1; ring }
  have hnorm_sq : ∀ x : E n, ‖map x‖ ^ 2 = ‖x‖ ^ 2 := by
    intro x
    dsimp [map]
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_smul_right,
      real_inner_comm x v]
    have hv_ne : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
    have hc : c = 2 / ‖v‖ ^ 2 := rfl
    rw [hc]
    field_simp
    ring
  have hinvol : ∀ x : E n, map (map x) = x := by
    intro x
    dsimp [map]
    rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
    have hv_ne : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
    have hcoeff : c * (inner ℝ v x - c * inner ℝ v x * ‖v‖ ^ 2) = -(c * inner ℝ v x) := by
      have hc : c = 2 / ‖v‖ ^ 2 := rfl
      rw [hc]; field_simp; ring
    rw [hcoeff, neg_smul, sub_neg_eq_add, sub_add_cancel]
  { toLinearEquiv :=
      { toFun := map
        invFun := map
        left_inv := hinvol
        right_inv := hinvol
        map_add' := map.map_add'
        map_smul' := map.map_smul' }
    norm_map' := fun x => by
      change ‖map x‖ = ‖x‖
      have hsq := hnorm_sq x
      rw [← Real.sqrt_sq (norm_nonneg (map x)), hsq, Real.sqrt_sq (norm_nonneg x)] }

lemma exists_isom_unit_to_unit {n : ℕ} (u w : E n) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
    ∃ R : E n ≃ₗᵢ[ℝ] E n, R u = w := by
  by_cases h : u = w
  · subst h; exact ⟨LinearIsometryEquiv.refl ℝ (E n), rfl⟩
  · have hv : u - w ≠ 0 := sub_ne_zero.mpr h
    refine ⟨householderReal (u - w) hv, ?_⟩
    change u - ((2 / ‖u - w‖ ^ 2) * inner ℝ (u - w) u) • (u - w) = w
    have hnorm : ‖u - w‖ ^ 2 = 2 * (1 - inner ℝ u w) := by
      rw [norm_sub_sq_real, hu, hw]; ring
    have hin : inner ℝ (u - w) u = 1 - inner ℝ u w := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq, hu, real_inner_comm]; ring
    have hv_ne : ‖u - w‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
    have hcoeff : (2 / ‖u - w‖ ^ 2) * inner ℝ (u - w) u = 1 := by
      rw [hnorm] at hv_ne
      rw [hin, hnorm]
      have hne1 : 1 - inner ℝ u w ≠ 0 := fun h0 => hv_ne (by rw [h0, mul_zero])
      field_simp
    rw [hcoeff, one_smul, sub_sub_cancel]

lemma hermCoeff_eq_coeff_nd {n : ℕ} (w : E n) (α : Fin n → ℕ) :
    hermCoeff w α = coeff_nd (fun x => (ltf w 0 x : ℝ)) α := by
  unfold hermCoeff coeff_nd γ
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  have hprod : Hnd α x = ∏ i : Fin n, Polynomial.aeval (x i) (Polynomial.hermite (α i)) /
      Real.sqrt ((α i).factorial) := by
    unfold Hnd
    refine Finset.prod_congr rfl fun i _ => h1D_eq_div (α i) (x i)
  dsimp only
  rw [← hprod, mul_comm]

lemma memLp_ltf {n : ℕ} (w : E n) : MemLp (fun x : E n => (ltf w 0 x : ℝ)) 2 (γ n) := by
  have hmeas : Measurable (fun x : E n => (ltf w 0 x : ℝ)) := by
    unfold ltf sgn
    exact measurable_from_top.comp
      (Measurable.ite (measurableSet_le measurable_const (by fun_prop)) measurable_const measurable_const)
  refine MemLp.of_bound hmeas.aestronglyMeasurable 1 (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs]
  simp only [ltf, sgn]; split_ifs <;> norm_num

lemma coeff_nd_single_zero {n : ℕ} (hn : 1 ≤ n) (α : Fin n → ℕ) :
    coeff_nd (fun x : E n => (ltf (EuclideanSpace.single (⟨0, hn⟩ : Fin n) 1) 0 x : ℝ)) α =
      if ∀ i : Fin n, i ≠ ⟨0, hn⟩ → α i = 0 then coeff1D (α ⟨0, hn⟩) else 0 := by
  let i₀ : Fin n := ⟨0, hn⟩
  let e₀ : E n := EuclideanSpace.single i₀ 1
  unfold coeff_nd
  rw [γ, ← ProbabilityTheory.map_pi_eq_stdGaussian,
    integral_map (PiLp.lipschitzWith_toLp 2 (fun _ : Fin n => ℝ)).continuous.measurable.aemeasurable]
  · have heq : (fun x : Fin n → ℝ =>
          Hnd α (WithLp.toLp 2 x) * (ltf e₀ 0 (WithLp.toLp 2 x) : ℝ)) =
        fun x => ∏ i : Fin n,
          (if i = i₀ then (sgn (x i) : ℝ) * h1D (α i) (x i) else h1D (α i) (x i)) := by
      ext x
      have hin : inner ℝ e₀ (WithLp.toLp 2 x) = x i₀ := by
        simp [e₀, EuclideanSpace.inner_single_left]
      have hltf : (ltf e₀ 0 (WithLp.toLp 2 x) : ℝ) = (sgn (x i₀) : ℝ) := by
        simp [ltf, hin]
      rw [hltf, Hnd]
      change (∏ i : Fin n, h1D (α i) (x i)) * (sgn (x i₀) : ℝ) = _
      rw [← Finset.mul_prod_erase Finset.univ (fun i => h1D (α i) (x i)) (Finset.mem_univ i₀),
        ← Finset.mul_prod_erase Finset.univ
          (fun i => if i = i₀ then (sgn (x i) : ℝ) * h1D (α i) (x i) else h1D (α i) (x i))
          (Finset.mem_univ i₀)]
      simp only [↓reduceIte]
      have hrest : (∏ i ∈ Finset.univ.erase i₀, h1D (α i) (x i)) =
          ∏ i ∈ Finset.univ.erase i₀,
            (if i = i₀ then (sgn (x i) : ℝ) * h1D (α i) (x i) else h1D (α i) (x i)) := by
        refine Finset.prod_congr rfl fun i hi => ?_
        rw [if_neg (Finset.ne_of_mem_erase hi)]
      rw [hrest]; ring
    change ∫ x : Fin n → ℝ, Hnd α (WithLp.toLp 2 x) * (ltf e₀ 0 (WithLp.toLp 2 x) : ℝ) ∂_ = _
    rw [heq, integral_fintype_prod_eq_prod
      (f := fun i t => if i = i₀ then (sgn t : ℝ) * h1D (α i) t else h1D (α i) t)]
    have hfac : ∀ i : Fin n,
        (∫ t : ℝ, (if i = i₀ then (sgn t : ℝ) * h1D (α i) t else h1D (α i) t) ∂
          (ProbabilityTheory.gaussianReal 0 1)) =
        if i = i₀ then coeff1D (α i₀) else if α i = 0 then 1 else 0 := by
      intro i
      by_cases hi : i = i₀
      · subst hi; simp [coeff1D]
      · simp only [hi, ↓reduceIte]
        have h := h1D_orthonormal (α i) 0
        simpa [h1D_zero_fn] using h
    simp_rw [hfac]
    by_cases hall : ∀ i : Fin n, i ≠ i₀ → α i = 0
    · rw [if_pos hall, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
      simp only [↓reduceIte]
      have hones : ∏ i ∈ Finset.univ.erase i₀,
          (if i = i₀ then coeff1D (α i₀) else if α i = 0 then 1 else 0) = 1 := by
        refine Finset.prod_eq_one fun i hi => ?_
        have hne := Finset.ne_of_mem_erase hi
        rw [if_neg hne, if_pos (hall i hne)]
      rw [hones, mul_one]
    · rw [if_neg hall]
      push Not at hall
      obtain ⟨i, hne, hnz⟩ := hall
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hne, hnz])
  · have hm : AEStronglyMeasurable (fun x : E n => Hnd α x * (ltf e₀ 0 x : ℝ)) (γ n) :=
      ((continuous_Hnd α).aestronglyMeasurable).mul (memLp_ltf _).1
    rwa [γ, ← ProbabilityTheory.map_pi_eq_stdGaussian] at hm

/-! ### Part 3: Explicit Multivariate Hermite Formula for `hermCoeff w α` -/

lemma integral_poly_mul_h1D_le (r : ℕ) :
    ∀ (P : ℝ[X]), P.natDegree ≤ r →
      ∫ x : ℝ, P.eval x * h1D r x * phi x = P.coeff r * Real.sqrt (r.factorial : ℝ) := by
  induction r with
  | zero =>
    intro P hdeg
    have hP : P = Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hdeg
    conv_lhs => rw [hP]
    simp only [Polynomial.eval_C, h1D_zero_fn, mul_one, integral_const_mul,
      Nat.factorial_zero, Nat.cast_one, Real.sqrt_one]
    have hphi : ∫ a : ℝ, phi a = 1 := ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 one_ne_zero
    rw [hphi, mul_one]
  | succ m ih =>
    intro P hdeg
    rw [integral_poly_mul_h1D_succ P m]
    have hd : P.derivative.natDegree ≤ m :=
      (Polynomial.natDegree_derivative_le (p := P)).trans (by omega)
    rw [ih P.derivative hd, Polynomial.coeff_derivative]
    have hpos : (0 : ℝ) < m + 1 := by positivity
    have hfac : Real.sqrt ((m + 1).factorial : ℝ) =
        Real.sqrt (m + 1 : ℝ) * Real.sqrt (m.factorial : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Real.sqrt_mul hpos.le]
    have hsq : (Real.sqrt (m + 1 : ℝ))⁻¹ * ((m : ℝ) + 1) = Real.sqrt (m + 1 : ℝ) := by
      have hne : Real.sqrt (m + 1 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
      rw [inv_mul_eq_iff_eq_mul₀ hne, Real.mul_self_sqrt hpos.le]
    rw [hfac]
    calc (Real.sqrt ((m : ℝ) + 1))⁻¹ * (P.coeff (m + 1) * ((m : ℝ) + 1) * Real.sqrt (m.factorial : ℝ))
        = P.coeff (m + 1) * (((Real.sqrt ((m : ℝ) + 1))⁻¹ * ((m : ℝ) + 1)) * Real.sqrt (m.factorial : ℝ)) := by ring
      _ = P.coeff (m + 1) * (Real.sqrt ((m : ℝ) + 1) * Real.sqrt (m.factorial : ℝ)) := by rw [hsq]

lemma integral_pow_mul_h1D_gaussianReal (b r : ℕ) (hbr : b ≤ r) :
    ∫ x : ℝ, x ^ b * h1D r x ∂(ProbabilityTheory.gaussianReal 0 1) =
      if b = r then Real.sqrt (r.factorial : ℝ) else 0 := by
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul one_ne_zero]
  have heq : (fun x : ℝ => ProbabilityTheory.gaussianPDFReal 0 1 x • (x ^ b * h1D r x)) =
      fun x => (Polynomial.X ^ b : ℝ[X]).eval x * h1D r x * phi x := by
    ext x; simp [phi, smul_eq_mul]; ring
  rw [heq, integral_poly_mul_h1D_le r (Polynomial.X ^ b) (by simp; exact hbr)]
  simp only [Polynomial.coeff_X_pow]
  by_cases h : b = r
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h), zero_mul]

lemma hermite_monic_coeff (r : ℕ) :
    (Polynomial.hermite r).coeff r = 1 ∧ (Polynomial.hermite r).natDegree ≤ r := by
  refine ⟨?_, (Polynomial.natDegree_hermite (n := r)).le⟩
  have h := Polynomial.coeff_hermite_explicit 0 r
  simp only [mul_zero, zero_add, pow_zero, Nat.zero_sub, Nat.cast_one, Nat.choose_self, mul_one] at h
  change ((Polynomial.hermite r).coeff r : ℤ) = 1
  exact h.trans (by decide)

lemma integral_Hnd_mul_mem_P_Hnd_lt {n : ℕ} (α : Fin n → ℕ) (m : ℕ) (hm : m < totalDeg α)
    {p : E n → ℝ} (hp : p ∈ P_Hnd n m) :
    ∫ y : E n, Hnd α y * p y ∂(γ n) = 0 := by
  induction hp using Submodule.span_induction with
  | mem q hq =>
    rcases hq with ⟨β, hβ, rfl⟩
    have hdeg : totalDeg β ≤ m := mem_I_deg.mp hβ
    have hne : α ≠ β := fun h => by subst h; omega
    rw [Hnd_orthonormal α β, if_neg hne]
  | zero => simp
  | add x y hx hy ihx ihy =>
    have h1 := integrable_mul_of_memLp_two (memLp_Hnd α) (P_Hnd_memLp hx)
    have h2 := integrable_mul_of_memLp_two (memLp_Hnd α) (P_Hnd_memLp hy)
    have hadd : (fun g : E n => Hnd α g * (x + y) g) =
        fun g => Hnd α g * x g + Hnd α g * y g := by ext g; simp [mul_add]
    rw [hadd, integral_add h1 h2, ihx, ihy, add_zero]
  | smul c x _ ihx =>
    have hsm : (fun g : E n => Hnd α g * (c • x) g) =
        fun g => c * (Hnd α g * x g) := by ext g; simp [smul_eq_mul]; ring
    rw [hsm, integral_const_mul, ihx, mul_zero]

lemma integral_Hnd_mul_inner_pow {n : ℕ} (α : Fin n → ℕ) (w : E n) :
    ∫ y : E n, Hnd α y * (inner ℝ y w) ^ totalDeg α ∂(γ n) =
      ((totalDeg α).factorial : ℝ) / Real.sqrt (∏ i : Fin n, ((α i).factorial : ℝ)) *
        ∏ i : Fin n, w i ^ α i := by
  let k := totalDeg α
  have hinner_pow : ∀ y : E n, (inner ℝ y w) ^ k =
      ∑ β ∈ (Finset.univ : Finset (Fin n)).piAntidiag k,
        (Nat.multinomial Finset.univ β : ℝ) * (∏ i : Fin n, w i ^ β i) *
          (∏ i : Fin n, y i ^ β i) := by
    intro y
    have hin : inner ℝ y w = ∑ i : Fin n, w i * y i := by
      simp [PiLp.inner_apply, RCLike.inner_apply]
    rw [hin, Finset.sum_pow_eq_sum_piAntidiag]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [mul_pow, Finset.prod_mul_distrib]
    ring
  have hintegrand : (fun y : E n => Hnd α y * (inner ℝ y w) ^ k) =
      fun y => ∑ β ∈ (Finset.univ : Finset (Fin n)).piAntidiag k,
        ((Nat.multinomial Finset.univ β : ℝ) * (∏ i : Fin n, w i ^ β i)) *
          (Hnd α y * ∏ i : Fin n, y i ^ β i) := by
    ext y
    rw [hinner_pow y, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => by ring
  have hint_term : ∀ β : Fin n → ℕ,
      Integrable (fun y : E n => Hnd α y * ∏ i : Fin n, y i ^ β i) (γ n) := by
    intro β
    rw [γ, ← ProbabilityTheory.map_pi_eq_stdGaussian]
    refine (integrable_map_measure ?_
      (PiLp.lipschitzWith_toLp 2 (fun _ : Fin n => ℝ)).continuous.measurable.aemeasurable).mpr ?_
    · refine ((continuous_Hnd α).mul ?_).aestronglyMeasurable
      refine continuous_finsetProd _ fun i _ =>
        ((PiLp.continuous_apply 2 (fun _ => ℝ) i).pow (β i))
    · have heq : (fun x : Fin n → ℝ => Hnd α (WithLp.toLp 2 x) * ∏ i : Fin n, (WithLp.toLp 2 x) i ^ β i) =
          fun x => ∏ i : Fin n, (h1D (α i) (x i) * x i ^ β i) := by
        ext x; simp [Hnd, Finset.prod_mul_distrib]
      change Integrable (fun x : Fin n → ℝ => Hnd α (WithLp.toLp 2 x) * ∏ i : Fin n, (WithLp.toLp 2 x) i ^ β i) _
      rw [heq]
      refine integrable_pi_fin_prod (fun i t => h1D (α i) t * t ^ β i) fun i => ?_
      have hm : Measurable (fun t : ℝ => h1D (α i) t * t ^ β i) :=
        (continuous_h1D (α i)).measurable.mul (continuous_pow (β i)).measurable
      refine integrable_gaussianReal_of_mul_phi hm.aestronglyMeasurable ?_
      let P : Polynomial ℝ := Polynomial.C (Real.sqrt ((α i).factorial : ℝ))⁻¹ *
        ((Polynomial.hermite (α i)).map (algebraMap ℤ ℝ) * Polynomial.X ^ β i)
      have hfn : (fun t : ℝ => (h1D (α i) t * t ^ β i) * phi t) = fun t => P.eval t * phi t := by
        ext t
        simp only [P, h1D, Hpoly, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.aeval_def, Polynomial.eval_map]
        ring
      rw [hfn]
      exact integrable_poly_mul_phi P
  rw [hintegrand, integral_finsetSum _ fun β _ => (hint_term β).const_mul _]
  simp_rw [integral_const_mul]
  have hterm_val : ∀ β ∈ (Finset.univ : Finset (Fin n)).piAntidiag k,
      (∫ y : E n, Hnd α y * ∏ i : Fin n, y i ^ β i ∂(γ n)) =
        if β = α then Real.sqrt (∏ i : Fin n, ((α i).factorial : ℝ)) else 0 := by
    intro β hβ
    have hsum_eq : ∑ i : Fin n, β i = ∑ i : Fin n, α i := by
      have hmem := Finset.mem_piAntidiag.mp hβ
      exact hmem.1
    have heq : (fun x : Fin n → ℝ => Hnd α (WithLp.toLp 2 x) * ∏ i : Fin n, (WithLp.toLp 2 x) i ^ β i) =
        fun x => ∏ i : Fin n, (x i ^ β i * h1D (α i) (x i)) := by
      ext x; simp [Hnd, Finset.prod_mul_distrib, mul_comm]
    rw [γ, ← ProbabilityTheory.map_pi_eq_stdGaussian]
    have hm_int : AEStronglyMeasurable (fun y : E n => Hnd α y * ∏ i : Fin n, y i ^ β i)
        (Measure.map (WithLp.toLp 2) (Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)) :=
      ((continuous_Hnd α).mul (continuous_finsetProd _ fun i _ =>
        ((PiLp.continuous_apply 2 (fun _ => ℝ) i).pow (β i)))).aestronglyMeasurable
    rw [integral_map (PiLp.lipschitzWith_toLp 2 (fun _ : Fin n => ℝ)).continuous.measurable.aemeasurable hm_int]
    change ∫ x : Fin n → ℝ, Hnd α (WithLp.toLp 2 x) * ∏ i : Fin n, (WithLp.toLp 2 x) i ^ β i ∂_ = _
    rw [heq, integral_fintype_prod_eq_prod (f := fun i t => t ^ β i * h1D (α i) t)]
    by_cases hβα : β = α
    · subst hβα
      rw [if_pos rfl]
      have hfac : ∀ i : Fin n,
          ∫ t : ℝ, t ^ β i * h1D (β i) t ∂(ProbabilityTheory.gaussianReal 0 1) =
            Real.sqrt ((β i).factorial : ℝ) := fun i => by
        simpa using integral_pow_mul_h1D_gaussianReal (β i) (β i) le_rfl
      simp_rw [hfac]
      exact (Real.sqrt_prod Finset.univ (x := fun i => ((β i).factorial : ℝ))
        (fun _ _ => Nat.cast_nonneg _)).symm
    · rw [if_neg hβα]
      have hlt : ∃ i : Fin n, β i < α i := by
        by_contra hge
        push Not at hge
        have hle : ∀ i ∈ Finset.univ, α i ≤ β i := fun i _ => hge i
        have heq_coord : ∀ i ∈ Finset.univ, α i = β i :=
          (Finset.sum_eq_sum_iff_of_le hle).mp hsum_eq.symm
        exact hβα (funext fun i => (heq_coord i (Finset.mem_univ i)).symm)
      obtain ⟨i₀, hi₀⟩ := hlt
      refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
      rw [integral_pow_mul_h1D_gaussianReal (β i₀) (α i₀) hi₀.le, if_neg hi₀.ne]
  have hα_mem : α ∈ (Finset.univ : Finset (Fin n)).piAntidiag k :=
    Finset.mem_piAntidiag.mpr ⟨rfl, fun _ _ => Finset.mem_univ _⟩
  have hsum_collapse :
      ∑ β ∈ (Finset.univ : Finset (Fin n)).piAntidiag k,
        ((Nat.multinomial Finset.univ β : ℝ) * (∏ i : Fin n, w i ^ β i)) *
          (∫ y : E n, Hnd α y * ∏ i : Fin n, y i ^ β i ∂(γ n)) =
      ((Nat.multinomial Finset.univ α : ℝ) * (∏ i : Fin n, w i ^ α i)) *
        Real.sqrt (∏ i : Fin n, ((α i).factorial : ℝ)) := by
    rw [Finset.sum_eq_single α]
    · rw [hterm_val α hα_mem, if_pos rfl]
    · intro β hβ hne
      rw [hterm_val β hβ, if_neg hne, mul_zero]
    · intro hnot; exact absurd hα_mem hnot
  rw [hsum_collapse]
  have hmult : (Nat.multinomial Finset.univ α : ℝ) * ∏ i : Fin n, ((α i).factorial : ℝ) = (k.factorial : ℝ) := by
    have hspec : Nat.multinomial Finset.univ α * ∏ i : Fin n, (α i).factorial = k.factorial := by
      simpa [k, totalDeg, mul_comm] using Nat.multinomial_spec Finset.univ α
    exact_mod_cast hspec
  have hprod_pos : (0 : ℝ) < ∏ i : Fin n, ((α i).factorial : ℝ) :=
    Finset.prod_pos fun i _ => Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hsqrt_ne : Real.sqrt (∏ i : Fin n, ((α i).factorial : ℝ)) ≠ 0 :=
    (Real.sqrt_pos.mpr hprod_pos).ne'
  have hdiv : (Nat.multinomial Finset.univ α : ℝ) * Real.sqrt (∏ i : Fin n, ((α i).factorial : ℝ)) =
      (k.factorial : ℝ) / Real.sqrt (∏ i : Fin n, ((α i).factorial : ℝ)) := by
    rw [eq_div_iff hsqrt_ne, mul_assoc, Real.mul_self_sqrt hprod_pos.le, hmult]
  calc ((Nat.multinomial Finset.univ α : ℝ) * (∏ i : Fin n, w i ^ α i)) *
        Real.sqrt (∏ i : Fin n, ((α i).factorial : ℝ))
      = ((Nat.multinomial Finset.univ α : ℝ) * Real.sqrt (∏ i : Fin n, ((α i).factorial : ℝ))) *
          (∏ i : Fin n, w i ^ α i) := by ring
    _ = (k.factorial : ℝ) / Real.sqrt (∏ i : Fin n, ((α i).factorial : ℝ)) *
          (∏ i : Fin n, w i ^ α i) := by rw [hdiv]

lemma memLp_pow_inner {n : ℕ} (w : E n) (k : ℕ) :
    MemLp (fun y : E n => (inner ℝ y w) ^ k) 2 (γ n) := by
  have h : (fun y : E n => (inner ℝ y w) ^ k * (fun _ : E n => (1 : ℝ)) y) ∈ P_Hnd n (0 + k) :=
    mul_pow_inner_mem_P_Hnd w (one_mem_P_Hnd n)
  simpa only [mul_one] using P_Hnd_memLp h

lemma memLp_poly_inner {n : ℕ} (P : ℝ[X]) (m : ℕ) (hdeg : P.natDegree ≤ m) (w : E n) :
    MemLp (fun y : E n => P.eval (inner ℝ y w)) 2 (γ n) := by
  have h : (fun y : E n => P.eval (inner ℝ y w) * (fun _ : E n => (1 : ℝ)) y) ∈ P_Hnd n (0 + m) :=
    mul_poly_inner_mem_P_Hnd P m hdeg w (one_mem_P_Hnd n)
  simpa only [mul_one] using P_Hnd_memLp h

lemma integral_Hnd_mul_h1D_inner {n : ℕ} (α : Fin n → ℕ) (w : E n) (m : ℕ) (hm : m ≤ totalDeg α) :
    ∫ y : E n, Hnd α y * h1D m (inner ℝ y w) ∂(γ n) =
      if m = totalDeg α then
        Real.sqrt (((totalDeg α).factorial : ℝ) / ∏ i : Fin n, ((α i).factorial : ℝ)) *
          ∏ i : Fin n, w i ^ α i
      else 0 := by
  by_cases hmeq : m = totalDeg α
  · subst hmeq
    rw [if_pos rfl]
    let P_h : ℝ[X] := (Polynomial.hermite (totalDeg α)).map (algebraMap ℤ ℝ)
    let Q : ℝ[X] := P_h - Polynomial.X ^ (totalDeg α)
    have hP_eval : ∀ t : ℝ, h1D (totalDeg α) t =
        (Real.sqrt ((totalDeg α).factorial : ℝ))⁻¹ * (t ^ totalDeg α + Q.eval t) := by
      intro t
      have h1 : P_h.eval t = Hpoly (totalDeg α) t := by
        simp [P_h, Hpoly, Polynomial.aeval_def, Polynomial.eval_map]
      simp only [h1D, ← h1, Q, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
      ring
    have hQ_zero : ∫ y : E n, Hnd α y * Q.eval (inner ℝ y w) ∂(γ n) = 0 := by
      by_cases hk0 : totalDeg α = 0
      · have hQ0 : Q = 0 := by
          simp [Q, P_h, hk0]
        simp [hQ0]
      · have hPdeg : P_h.natDegree ≤ totalDeg α :=
          (Polynomial.natDegree_map_le).trans (hermite_monic_coeff (totalDeg α)).2
        have hPcoeff : P_h.coeff (totalDeg α) = 1 := by
          simp [P_h, (hermite_monic_coeff (totalDeg α)).1]
        have hQdeg : Q.natDegree ≤ totalDeg α - 1 := by
          by_cases hQ0 : Q = 0
          · simp [hQ0]
          · have hlt : Q.natDegree < totalDeg α := by
              refine Polynomial.natDegree_lt_iff_degree_lt hQ0 |>.mpr ?_
              have hdeg_le : Q.degree ≤ (totalDeg α : WithBot ℕ) := by
                refine le_trans (Polynomial.degree_sub_le _ _) (max_le ?_ ?_)
                · exact (Polynomial.degree_le_iff_coeff_zero _ _).mpr fun n hn => by
                    have hgt : totalDeg α < n := WithBot.coe_lt_coe.mp hn
                    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hPdeg hgt)
                · exact Polynomial.degree_X_pow_le _
              refine lt_of_le_of_ne hdeg_le ?_
              intro heq
              have hcoeff0 : Q.coeff (totalDeg α) = 0 := by
                simp [Q, hPcoeff]
              have hnat : Q.natDegree = totalDeg α := Polynomial.natDegree_eq_of_degree_eq_some heq
              have hlead : Q.coeff Q.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ0
              rw [hnat] at hlead
              exact hlead hcoeff0
            omega
        have hQ_mem : (fun y : E n => Q.eval (inner ℝ y w)) ∈ P_Hnd n (totalDeg α - 1) := by
          have h := mul_poly_inner_mem_P_Hnd Q (totalDeg α - 1) hQdeg w (one_mem_P_Hnd n)
          rw [zero_add] at h
          have heq : (fun g : E n => Q.eval (inner ℝ g w) * (fun _ : E n => (1 : ℝ)) g) =
              fun y => Q.eval (inner ℝ y w) := by ext y; simp
          rwa [heq] at h
        exact integral_Hnd_mul_mem_P_Hnd_lt α (totalDeg α - 1) (by omega) hQ_mem
    have hint_pow : Integrable (fun y : E n => Hnd α y * (inner ℝ y w) ^ totalDeg α) (γ n) :=
      integrable_mul_of_memLp_two (memLp_Hnd α) (memLp_pow_inner w (totalDeg α))
    have hint_Q : Integrable (fun y : E n => Hnd α y * Q.eval (inner ℝ y w)) (γ n) := by
      have hQd : Q.natDegree ≤ totalDeg α :=
        le_trans (Polynomial.natDegree_sub_le _ _)
          (max_le ((Polynomial.natDegree_map_le).trans (hermite_monic_coeff _).2) (by simp))
      exact integrable_mul_of_memLp_two (memLp_Hnd α) (memLp_poly_inner Q (totalDeg α) hQd w)
    have heq : (fun y : E n => Hnd α y * h1D (totalDeg α) (inner ℝ y w)) =
        fun y => (Real.sqrt ((totalDeg α).factorial : ℝ))⁻¹ *
          (Hnd α y * (inner ℝ y w) ^ totalDeg α + Hnd α y * Q.eval (inner ℝ y w)) := by
      ext y; rw [hP_eval]; ring
    rw [heq, integral_const_mul, integral_add hint_pow hint_Q, hQ_zero, add_zero,
      integral_Hnd_mul_inner_pow α w]
    have hk_pos : (0 : ℝ) < (totalDeg α).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hp_pos : (0 : ℝ) < ∏ i : Fin n, ((α i).factorial : ℝ) :=
      Finset.prod_pos fun i _ => Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hsq_k : (Real.sqrt ((totalDeg α).factorial : ℝ))⁻¹ * ((totalDeg α).factorial : ℝ) =
        Real.sqrt ((totalDeg α).factorial : ℝ) := by
      have hne : Real.sqrt ((totalDeg α).factorial : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hk_pos).ne'
      rw [inv_mul_eq_iff_eq_mul₀ hne, Real.mul_self_sqrt hk_pos.le]
    rw [Real.sqrt_div hk_pos.le]
    calc (Real.sqrt ((totalDeg α).factorial : ℝ))⁻¹ *
          (((totalDeg α).factorial : ℝ) / Real.sqrt (∏ i : Fin n, ((α i).factorial : ℝ)) *
            ∏ i : Fin n, w i ^ α i)
        = (((Real.sqrt ((totalDeg α).factorial : ℝ))⁻¹ * ((totalDeg α).factorial : ℝ)) /
            Real.sqrt (∏ i : Fin n, ((α i).factorial : ℝ))) * ∏ i : Fin n, w i ^ α i := by ring
      _ = (Real.sqrt ((totalDeg α).factorial : ℝ) / Real.sqrt (∏ i : Fin n, ((α i).factorial : ℝ))) *
            ∏ i : Fin n, w i ^ α i := by rw [hsq_k]
  · rw [if_neg hmeq]
    obtain ⟨P, hPdeg, hPeq⟩ := exists_poly_h1D m
    have hp_mem : (fun y : E n => h1D m (inner ℝ y w)) ∈ P_Hnd n m := by
      have h := mul_poly_inner_mem_P_Hnd P m hPdeg w (one_mem_P_Hnd n)
      rw [zero_add] at h
      have heq : (fun g : E n => P.eval (inner ℝ g w) * (fun _ : E n => (1 : ℝ)) g) =
          fun y => h1D m (inner ℝ y w) := by ext y; simp [hPeq]
      rwa [heq] at h
    exact integral_Hnd_mul_mem_P_Hnd_lt α m (lt_of_le_of_ne hm hmeq) hp_mem

lemma hermCoeff_formula {n : ℕ} (hn : 1 ≤ n) (w : E n) (hw : ‖w‖ = 1) (α : Fin n → ℕ) :
    hermCoeff w α =
      coeff1D (totalDeg α) *
        Real.sqrt (((totalDeg α).factorial : ℝ) / ∏ i : Fin n, ((α i).factorial : ℝ)) *
        ∏ i : Fin n, w i ^ α i := by
  let i₀ : Fin n := ⟨0, hn⟩
  let e₀ : E n := EuclideanSpace.single i₀ 1
  have he₀ : ‖e₀‖ = 1 := by simp [e₀]
  obtain ⟨R, hR⟩ := exists_isom_unit_to_unit e₀ w he₀ hw
  have hmp : MeasurePreserving R (γ n) (γ n) := measurePreserving_isom_γ R
  have hltf_comp : ∀ x : E n, (ltf w 0 (R x) : ℝ) = (ltf e₀ 0 x : ℝ) := by
    intro x
    simp only [ltf, sub_zero]
    rw [← hR, R.inner_map_map e₀ x]
  rw [hermCoeff_eq_coeff_nd]
  unfold coeff_nd
  have hchg : ∫ y : E n, Hnd α y * (ltf w 0 y : ℝ) ∂(γ n) =
      ∫ x : E n, Hnd α (R x) * (ltf e₀ 0 x : ℝ) ∂(γ n) := by
    calc ∫ y : E n, Hnd α y * (ltf w 0 y : ℝ) ∂(γ n)
        = ∫ x : E n, Hnd α (R x) * (ltf w 0 (R x) : ℝ) ∂(γ n) :=
          (hmp.integral_comp R.toHomeomorph.measurableEmbedding (fun y => Hnd α y * (ltf w 0 y : ℝ))).symm
      _ = ∫ x : E n, Hnd α (R x) * (ltf e₀ 0 x : ℝ) ∂(γ n) := by
          refine integral_congr_ae (ae_of_all _ fun x => congrArg (Hnd α (R x) * ·) (hltf_comp x))
  rw [hchg]
  let k := totalDeg α
  let fR : E n → ℝ := Hnd α ∘ R
  have hfR_mem : fR ∈ P_Hnd n k := Hnd_comp_isom_mem_P_Hnd α R
  let q : E n → ℝ := fun x => fR x - projFin fR k x
  have hq_mem : q ∈ P_Hnd n k := (P_Hnd n k).sub_mem hfR_mem (projFin_mem_P_Hnd fR k)
  have hq_sq0 : ∫ x : E n, (q x) ^ 2 ∂(γ n) = 0 := by
    simpa [sq] using integral_projFin_orth (P_Hnd_memLp hfR_mem) k hq_mem
  have hae0 : q =ᵐ[γ n] 0 := by
    have h := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg (q x))
      ((P_Hnd_memLp hq_mem).integrable_sq)).mp hq_sq0
    filter_upwards [h] with x hx
    exact sq_eq_zero_iff.mp hx
  have hae_eq : (fun x : E n => Hnd α (R x) * (ltf e₀ 0 x : ℝ)) =ᵐ[γ n]
      fun x => projFin fR k x * (ltf e₀ 0 x : ℝ) := by
    filter_upwards [hae0] with x hx
    have : fR x = projFin fR k x := sub_eq_zero.mp hx
    change fR x * (ltf e₀ 0 x : ℝ) = projFin fR k x * (ltf e₀ 0 x : ℝ)
    rw [this]
  rw [integral_congr_ae hae_eq]
  have hsum_fn : (fun x : E n => projFin fR k x * (ltf e₀ 0 x : ℝ)) =
      fun x => ∑ β ∈ I_deg n k, coeff_nd fR β * (Hnd β x * (ltf e₀ 0 x : ℝ)) := by
    ext x
    simp only [projFin, Finset.sum_mul]
    refine Finset.sum_congr rfl fun β _ => by ring
  rw [hsum_fn, integral_finsetSum _ fun β _ =>
    (integrable_mul_of_memLp_two (memLp_Hnd β) (memLp_ltf e₀)).const_mul _]
  simp_rw [integral_const_mul]
  let β₀ : Fin n → ℕ := fun i => if i = i₀ then k else 0
  have hβ₀_mem : β₀ ∈ I_deg n k := by
    rw [mem_I_deg]
    unfold totalDeg β₀
    simp
  have hβ_zero : ∀ β ∈ I_deg n k, β ≠ β₀ →
      coeff_nd fR β * (∫ x : E n, Hnd β x * (ltf e₀ 0 x : ℝ) ∂(γ n)) = 0 := by
    intro β hβ hne
    change coeff_nd fR β * coeff_nd (fun x => (ltf e₀ 0 x : ℝ)) β = 0
    rw [coeff_nd_single_zero hn β]
    by_cases hall : ∀ i : Fin n, i ≠ i₀ → β i = 0
    · rw [if_pos hall]
      have hm_le : β i₀ ≤ k := by
        have hmem := mem_I_deg.mp hβ
        have hdeg : totalDeg β = β i₀ := by
          unfold totalDeg
          rw [← Finset.add_sum_erase Finset.univ β (Finset.mem_univ i₀)]
          have hs0 : ∑ i ∈ Finset.univ.erase i₀, β i = 0 :=
            Finset.sum_eq_zero fun i hi => hall i (Finset.ne_of_mem_erase hi)
          rw [hs0, add_zero]
        omega
      have hm_ne : β i₀ ≠ k := by
        intro heq
        apply hne
        ext i
        by_cases hi : i = i₀
        · subst hi; simp [β₀, heq]
        · simp [β₀, hi, hall i hi]
      have hHnd_β : ∀ x : E n, Hnd β x = h1D (β i₀) (inner ℝ x e₀) := by
        intro x
        have hin : inner ℝ x e₀ = x i₀ := by
          rw [real_inner_comm]; simp [e₀, EuclideanSpace.inner_single_left]
        rw [hin, Hnd, ← Finset.mul_prod_erase Finset.univ (fun i => h1D (β i) (x i)) (Finset.mem_univ i₀)]
        have hones : ∏ i ∈ Finset.univ.erase i₀, h1D (β i) (x i) = 1 :=
          Finset.prod_eq_one fun i hi => by rw [hall i (Finset.ne_of_mem_erase hi), h1D_zero_fn]
        rw [hones, mul_one]
      have hcoeff_fR : coeff_nd fR β = 0 := by
        unfold coeff_nd
        have hswap : (fun x : E n => Hnd β x * fR x) =
            fun x => Hnd α (R x) * h1D (β i₀) (inner ℝ (R x) w) := by
          ext x
          have hin : inner ℝ (R x) w = inner ℝ x e₀ := by
            rw [← hR, R.inner_map_map x e₀]
          rw [hin, hHnd_β x, mul_comm]
          rfl
        rw [hswap]
        have hcomp := hmp.integral_comp R.toHomeomorph.measurableEmbedding
          (fun y : E n => Hnd α y * h1D (β i₀) (inner ℝ y w))
        change ∫ x : E n, (fun y => Hnd α y * h1D (β i₀) (inner ℝ y w)) (R x) ∂(γ n) = 0
        rw [hcomp, integral_Hnd_mul_h1D_inner α w (β i₀) hm_le, if_neg hm_ne]
      rw [hcoeff_fR, zero_mul]
    · rw [if_neg hall, mul_zero]
  rw [Finset.sum_eq_single β₀]
  · have hHnd_β₀ : ∀ x : E n, Hnd β₀ x = h1D k (inner ℝ x e₀) := by
      intro x
      have hin : inner ℝ x e₀ = x i₀ := by
        rw [real_inner_comm]; simp [e₀, EuclideanSpace.inner_single_left]
      rw [hin, Hnd, ← Finset.mul_prod_erase Finset.univ (fun i => h1D (β₀ i) (x i)) (Finset.mem_univ i₀)]
      have hones : ∏ i ∈ Finset.univ.erase i₀, h1D (β₀ i) (x i) = 1 :=
        Finset.prod_eq_one fun i hi => by
          have : β₀ i = 0 := if_neg (Finset.ne_of_mem_erase hi)
          rw [this, h1D_zero_fn]
      simp [β₀, hones]
    have hcoeff_fR : coeff_nd fR β₀ =
        Real.sqrt ((k.factorial : ℝ) / ∏ i : Fin n, ((α i).factorial : ℝ)) *
          ∏ i : Fin n, w i ^ α i := by
      unfold coeff_nd
      have hswap : (fun x : E n => Hnd β₀ x * fR x) =
          fun x => Hnd α (R x) * h1D k (inner ℝ (R x) w) := by
        ext x
        have hin : inner ℝ (R x) w = inner ℝ x e₀ := by
          rw [← hR, R.inner_map_map x e₀]
        rw [hin, hHnd_β₀ x, mul_comm]
        rfl
      rw [hswap]
      have hcomp := hmp.integral_comp R.toHomeomorph.measurableEmbedding
        (fun y : E n => Hnd α y * h1D k (inner ℝ y w))
      change ∫ x : E n, (fun y => Hnd α y * h1D k (inner ℝ y w)) (R x) ∂(γ n) = _
      rw [hcomp, integral_Hnd_mul_h1D_inner α w k le_rfl, if_pos rfl]
    have hcoeff_ltf : ∫ x : E n, Hnd β₀ x * (ltf e₀ 0 x : ℝ) ∂(γ n) = coeff1D k := by
      change coeff_nd (fun x => (ltf e₀ 0 x : ℝ)) β₀ = coeff1D k
      rw [coeff_nd_single_zero hn β₀, if_pos (fun i hi => if_neg (show i ≠ i₀ from hi))]
      simp [β₀, show (⟨0, hn⟩ : Fin n) = i₀ from rfl]
    rw [hcoeff_fR, hcoeff_ltf]
    ring
  · exact hβ_zero
  · intro hnot; exact absurd hβ₀_mem hnot

lemma p1D53_eq_sum_coeff1D_sq (K : ℕ) :
    p1D53 K = ∑ k ∈ Finset.Icc K (2 * K), (coeff1D k) ^ 2 := by
  unfold p1D53 bandWeight
  simp_rw [hermCoeff_eq_coeff_nd]
  have h1 : ∀ α : Fin 1 → Fin (2 * K + 1),
      coeff_nd (fun x => (ltf (EuclideanSpace.single (0 : Fin 1) 1) 0 x : ℝ))
          (fun i => (α i : ℕ)) =
        coeff1D (α 0) := by
    intro α
    have h := coeff_nd_single_zero (n := 1) (Nat.le_refl 1) (fun i => (α i : ℕ))
    have hall : ∀ i : Fin 1, i ≠ ⟨0, Nat.le_refl 1⟩ → (α i : ℕ) = 0 := fun i hi => by
      exfalso; exact hi (Subsingleton.elim _ _)
    rw [if_pos hall] at h
    exact h
  simp_rw [h1]
  have hsum : (∑ α : Fin 1 → Fin (2 * K + 1),
      if K ≤ ∑ i, (α i : ℕ) ∧ ∑ i, (α i : ℕ) ≤ 2 * K then (coeff1D (α 0)) ^ 2 else 0) =
      ∑ k ∈ Finset.Icc K (2 * K), (coeff1D k) ^ 2 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun α _ => (α 0 : ℕ)) ?_ ?_ ?_ ?_
    · intro α hα
      have hf := (Finset.mem_filter.mp hα).2
      rw [Fin.sum_univ_one] at hf
      exact Finset.mem_Icc.mpr hf
    · intro α _ β _ h
      ext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact h
    · intro k hk
      rw [Finset.mem_Icc] at hk
      refine ⟨fun _ => ⟨k, by omega⟩, ?_, rfl⟩
      simp [Finset.mem_filter, hk]
    · intro α _
      rfl
  exact hsum

end Aux_hermite_54

namespace Aux_channel_54

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open scoped ComplexConjugate

/-! ### 1. Basic `natToBits` / `splitReg` / `padKet` / `dirAmp` Helpers -/

lemma bitsToNat_natToBits_54 {q k : ℕ} (hk : k < 2 ^ q) :
    bitsToNat (natToBits q k) = k := by
  rw [← bitsEquivFin_apply]
  simp [natToBits, Nat.mod_eq_of_lt hk]

lemma natToBits_inj_of_lt {s a b : ℕ} (ha : a < 2 ^ s) (hb : b < 2 ^ s)
    (h : natToBits s a = natToBits s b) : a = b := by
  have := congrArg bitsToNat h
  rwa [bitsToNat_natToBits_54 ha, bitsToNat_natToBits_54 hb] at this

lemma splitReg_flatReg_54 (n b : ℕ) (f : Fin n → Qubits b) :
    splitReg n b (flatReg n b f) = f := by
  funext i j
  change f (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
    (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = f i j
  rw [finProdFinEquiv.symm_apply_apply]

lemma flatReg_splitReg_54 (n b : ℕ) (x : Qubits (n * b)) :
    flatReg n b (splitReg n b x) = x := by
  funext k
  change x (finProdFinEquiv (finProdFinEquiv.symm k)) = x k
  rw [finProdFinEquiv.apply_symm_apply]

lemma dirAmp_natToBits {n s : ℕ} (hns : n ≤ 2 ^ s) (w : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    dirAmp s w (natToBits s i.val) = ((w i : ℝ) : ℂ) := by
  unfold dirAmp
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have heq : natToBits s i.val ≠ natToBits s j.val := fun h =>
      hji (Fin.ext (natToBits_inj_of_lt (lt_of_lt_of_le i.isLt hns)
        (lt_of_lt_of_le j.isLt hns) h).symm)
    simp [heq]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma dirAmp_of_notMem {n s : ℕ} (w : EuclideanSpace ℝ (Fin n)) {b : Qubits s}
    (hb : ∀ i : Fin n, b ≠ natToBits s i.val) :
    dirAmp s w b = 0 := by
  unfold dirAmp
  exact Finset.sum_eq_zero fun i _ => if_neg (hb i)

lemma conj_dirAmp {n s : ℕ} (w : EuclideanSpace ℝ (Fin n)) (b : Qubits s) :
    conj (dirAmp s w b) = dirAmp s w b := by
  unfold dirAmp
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

lemma sum_normSq_dirAmp {n s : ℕ} (hns : n ≤ 2 ^ s) (w : EuclideanSpace ℝ (Fin n))
    (hw : ‖w‖ = 1) :
    ∑ b : Qubits s, dirAmp s w b * conj (dirAmp s w b) = 1 := by
  simp_rw [conj_dirAmp]
  let emb : Fin n ↪ Qubits s :=
    ⟨fun i => natToBits s i.val, fun i j h =>
      Fin.ext (natToBits_inj_of_lt (lt_of_lt_of_le i.isLt hns) (lt_of_lt_of_le j.isLt hns) h)⟩
  have hsplit : (Finset.univ : Finset (Qubits s)) =
      (Finset.univ : Finset (Fin n)).map emb ∪
        ((Finset.univ : Finset (Qubits s)) \ (Finset.univ : Finset (Fin n)).map emb) := by
    ext b; simp
  have hdisj : Disjoint ((Finset.univ : Finset (Fin n)).map emb)
      ((Finset.univ : Finset (Qubits s)) \ (Finset.univ : Finset (Fin n)).map emb) :=
    disjoint_sdiff_self_right
  rw [hsplit, Finset.sum_union hdisj]
  have hzero : ∑ b ∈ (Finset.univ : Finset (Qubits s)) \ (Finset.univ : Finset (Fin n)).map emb,
      dirAmp s w b * dirAmp s w b = 0 := by
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [Finset.mem_sdiff, Finset.mem_map] at hb
    have hnot : ∀ i : Fin n, b ≠ natToBits s i.val := fun i hi =>
      hb.2 ⟨i, Finset.mem_univ i, hi.symm⟩
    simp [dirAmp_of_notMem w hnot]
  rw [hzero, add_zero, Finset.sum_map]
  have hterm : ∑ i : Fin n, dirAmp s w (emb i) * dirAmp s w (emb i) =
      ∑ i : Fin n, ((w i ^ 2 : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    change dirAmp s w (natToBits s i.val) * dirAmp s w (natToBits s i.val) = _
    rw [dirAmp_natToBits hns w i]
    push_cast; ring
  rw [hterm, ← Complex.ofReal_sum]
  have hw2 : ∑ i : Fin n, w i ^ 2 = 1 := by
    have h := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => ℝ) w
    simp only [Real.norm_eq_abs, sq_abs, hw, one_pow] at h
    exact h.symm
  rw [hw2, Complex.ofReal_one]

lemma padKet_bandKet_eq_sum (n q K e : ℕ) (w : EuclideanSpace ℝ (Fin n)) :
    padKet e (bandKet n q K w) =
      ∑ α : Fin n → Fin (2 * K + 1),
        if K ≤ ∑ i, (α i : ℕ) ∧ ∑ i, (α i : ℕ) ≤ 2 * K then
          ((hermCoeff w (fun i => (α i : ℕ)) / Real.sqrt (bandWeight w K) : ℝ) : ℂ) •
            padKet e (ket (flatReg n q fun i => natToBits q (α i)))
        else 0 := by
  ext z
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  change (if ∀ j : Fin e, z (Fin.natAdd (n * q) j) = false then
      ∑ α : Fin n → Fin (2 * K + 1),
        if (fun i => z (Fin.castAdd e i)) = flatReg n q (fun i => natToBits q (α i)) ∧
            K ≤ ∑ i, (α i : ℕ) ∧ ∑ i, (α i : ℕ) ≤ 2 * K then
          ((hermCoeff w (fun i => (α i : ℕ)) / Real.sqrt (bandWeight w K) : ℝ) : ℂ)
        else 0
      else 0) =
    ∑ α : Fin n → Fin (2 * K + 1),
      (if K ≤ ∑ i, (α i : ℕ) ∧ ∑ i, (α i : ℕ) ≤ 2 * K then
        ((hermCoeff w (fun i => (α i : ℕ)) / Real.sqrt (bandWeight w K) : ℝ) : ℂ) •
          padKet e (ket (flatReg n q fun i => natToBits q (α i)))
      else 0) z
  split_ifs with hz
  · refine Finset.sum_congr rfl fun α _ => ?_
    by_cases hKα : K ≤ ∑ i, (α i : ℕ) ∧ ∑ i, (α i : ℕ) ≤ 2 * K
    · rw [if_pos hKα]
      simp only [PiLp.smul_apply, smul_eq_mul, padKet, if_pos hz, ket, PiLp.single_apply,
        hKα, and_true]
      by_cases hmatch : (fun i => z (Fin.castAdd e i)) = flatReg n q (fun i => natToBits q (α i))
      · rw [if_pos hmatch, if_pos hmatch, mul_one]
      · rw [if_neg hmatch, if_neg hmatch, mul_zero]
    · rw [if_neg hKα, if_neg (fun h => hKα h.2)]
      rfl
  · symm
    refine Finset.sum_eq_zero fun α _ => ?_
    split_ifs with hP
    · simp only [PiLp.smul_apply, smul_eq_mul, padKet]
      rw [if_neg hz, mul_zero]
    · rfl

lemma act_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (V : Matrix ι ι ℂ)
    {A : Type*} (s : Finset A) (f : A → EuclideanSpace ℂ ι) :
    act V (∑ a ∈ s, f a) = ∑ a ∈ s, act V (f a) :=
  map_sum (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) V) f s

lemma act_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (V : Matrix ι ι ℂ)
    (c : ℂ) (ψ : EuclideanSpace ℂ ι) :
    act V (c • ψ) = c • act V ψ :=
  map_smul (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) V) c ψ

/-! ### 2. Combinatorial Bijection & `V |bandKet⟩` Evaluation -/

def nonblankPos54 (n K : ℕ) (y : Qubits (2 * K * (Nat.clog 2 n + 1))) : Finset (Fin (2 * K)) :=
  Finset.univ.filter fun r : Fin (2 * K) =>
    (splitReg (2 * K) (Nat.clog 2 n + 1) y r) ⟨0, Nat.succ_pos _⟩ = false

def occVec54 (n K : ℕ) (y : Qubits (2 * K * (Nat.clog 2 n + 1))) (i : Fin n) : ℕ :=
  (Finset.univ.filter fun r : Fin (2 * K) =>
    splitReg (2 * K) (Nat.clog 2 n + 1) y r = natToBits (Nat.clog 2 n + 1) i.val).card

def blankCard54 (n K : ℕ) (y : Qubits (2 * K * (Nat.clog 2 n + 1))) : ℕ :=
  (Finset.univ.filter fun r : Fin (2 * K) =>
    splitReg (2 * K) (Nat.clog 2 n + 1) y r = blankSym54 (Nat.clog 2 n + 1)).card

def allValidSyms54 (n K : ℕ) (y : Qubits (2 * K * (Nat.clog 2 n + 1))) : Prop :=
  ∀ r : Fin (2 * K), ∃ j : Fin (n + 1),
    splitReg (2 * K) (Nat.clog 2 n + 1) y r = particleSym54 n (Nat.clog 2 n + 1) j

lemma occVec54_sum_add_blank_of_valid {n K : ℕ} (_hn : 1 ≤ n)
    (y : Qubits (2 * K * (Nat.clog 2 n + 1))) (hvalid : allValidSyms54 n K y) :
    (∑ i : Fin n, occVec54 n K y i) = (nonblankPos54 n K y).card ∧
      blankCard54 n K y = 2 * K - (nonblankPos54 n K y).card := by
  let s := Nat.clog 2 n + 1
  let fib : Fin n → Finset (Fin (2 * K)) := fun i =>
    Finset.univ.filter fun r => splitReg (2 * K) s y r = natToBits s i.val
  have hdisj : (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint fib := by
    intro i _ j _ hij
    change Disjoint (fib i) (fib j)
    rw [Finset.disjoint_left]
    intro r hri hrj
    rw [Finset.mem_filter] at hri hrj
    have heq : particleSym54 n s (Fin.castSucc i) = particleSym54 n s (Fin.castSucc j) := by
      simp only [particleSym54, Fin.val_castSucc, i.isLt, j.isLt, ↓reduceIte]
      exact hri.2.symm.trans hrj.2
    have hval : (Fin.castSucc i).val = (Fin.castSucc j).val :=
      congrArg (fun x : Fin (n + 1) => x.val) (particleSym54_inj n heq)
    exact hij (Fin.ext hval)
  have hbi : (Finset.univ : Finset (Fin n)).biUnion fib = nonblankPos54 n K y := by
    ext r
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter,
      nonblankPos54, fib]
    constructor
    · rintro ⟨i, hr⟩
      rw [hr]
      have hmsb := particleSym54_msb n (Fin.castSucc i)
      have hlt : (Fin.castSucc i).val < n := i.isLt
      rw [particleSym54_lt hlt] at hmsb
      simp only [Fin.val_castSucc] at hmsb
      rw [hmsb]
      simp [Nat.ne_of_lt i.isLt]
    · intro hmsb
      obtain ⟨j, hj⟩ := hvalid r
      have hmsb' := particleSym54_msb n j
      rw [← hj, hmsb] at hmsb'
      have hjn : j.val < n := by
        have : decide (j.val = n) = false := hmsb'.symm
        have hne : j.val ≠ n := of_decide_eq_false this
        omega
      refine ⟨⟨j.val, hjn⟩, ?_⟩
      rw [hj, particleSym54_lt hjn]
  have hsum : (∑ i : Fin n, occVec54 n K y i) = (nonblankPos54 n K y).card := by
    rw [← hbi, Finset.card_biUnion hdisj]
    rfl
  have hblank_eq : (Finset.univ.filter fun r : Fin (2 * K) => splitReg (2 * K) s y r = blankSym54 s) =
      Finset.univ \ nonblankPos54 n K y := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, nonblankPos54]
    constructor
    · intro hr hfalse
      have hmsb := particleSym54_msb n (Fin.last n)
      rw [particleSym54_last n s, ← hr] at hmsb
      change splitReg (2 * K) s y r ⟨0, Nat.succ_pos _⟩ = false at hfalse
      rw [hfalse] at hmsb
      exact Bool.false_ne_true (hmsb.trans (by simp))
    · intro hnot
      obtain ⟨j, hj⟩ := hvalid r
      have hmsb := particleSym54_msb n j
      rw [← hj] at hmsb
      have hjn : j.val = n := by
        by_contra hne
        have : (splitReg (2 * K) s y r) ⟨0, Nat.succ_pos _⟩ = false := by
          rw [hmsb]; simp [hne]
        exact hnot this
      have hjlast : j = Fin.last n := Fin.ext hjn
      rw [hj, hjlast, particleSym54_last]
  have hsub : nonblankPos54 n K y ⊆ Finset.univ := Finset.subset_univ _
  have hcard_sdiff : (Finset.univ \ nonblankPos54 n K y).card = 2 * K - (nonblankPos54 n K y).card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
    simp
  refine ⟨hsum, ?_⟩
  change (Finset.univ.filter fun r : Fin (2 * K) => splitReg (2 * K) s y r = blankSym54 s).card = _
  rw [hblank_eq, hcard_sdiff]

lemma multinomKet54_cond_iff {n K : ℕ} (hn : 1 ≤ n)
    (y : Qubits (2 * K * (Nat.clog 2 n + 1))) (α : Fin n → Fin (2 * K + 1))
    (hk : K ≤ ∑ i, (α i : ℕ) ∧ ∑ i, (α i : ℕ) ≤ 2 * K) :
    ((∀ i : Fin n, occVec54 n K y i = (α i : ℕ)) ∧
        blankCard54 n K y = 2 * K - ∑ i : Fin n, (α i : ℕ)) ↔
      allValidSyms54 n K y ∧ K ≤ (nonblankPos54 n K y).card ∧
        ∀ i : Fin n, (α i : ℕ) = occVec54 n K y i := by
  let s := Nat.clog 2 n + 1
  constructor
  · rintro ⟨hocc, hblank⟩
    let S : Fin (n + 1) → Finset (Fin (2 * K)) := fun j =>
      Finset.univ.filter fun r => splitReg (2 * K) s y r = particleSym54 n s j
    have hdisj : (↑(Finset.univ : Finset (Fin (n + 1))) : Set (Fin (n + 1))).PairwiseDisjoint S := by
      intro j₁ _ j₂ _ hj
      change Disjoint (S j₁) (S j₂)
      rw [Finset.disjoint_left]
      intro r hr₁ hr₂
      rw [Finset.mem_filter] at hr₁ hr₂
      exact hj (particleSym54_inj n (hr₁.2.symm.trans hr₂.2))
    have hcard_sum : ((Finset.univ : Finset (Fin (n + 1))).biUnion S).card = 2 * K := by
      rw [Finset.card_biUnion hdisj, Fin.sum_univ_castSucc]
      have hleft : (∑ i : Fin n, (S (Fin.castSucc i)).card) = ∑ i : Fin n, (α i : ℕ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hlt : (Fin.castSucc i).val < n := i.isLt
        have hsym : particleSym54 n s (Fin.castSucc i) = natToBits s i.val :=
          particleSym54_lt hlt
        change (Finset.univ.filter fun r => splitReg (2 * K) s y r = particleSym54 n s (Fin.castSucc i)).card = _
        rw [hsym]
        exact hocc i
      have hright : (S (Fin.last n)).card = 2 * K - ∑ i : Fin n, (α i : ℕ) := by
        change (Finset.univ.filter fun r => splitReg (2 * K) s y r = particleSym54 n s (Fin.last n)).card = _
        rw [particleSym54_last]
        exact hblank
      rw [hleft, hright]
      omega
    have huniv : (Finset.univ : Finset (Fin (n + 1))).biUnion S = Finset.univ := by
      refine Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_
      rw [hcard_sum]
      simp
    have hvalid : allValidSyms54 n K y := by
      intro r
      have hr : r ∈ (Finset.univ : Finset (Fin (n + 1))).biUnion S := by rw [huniv]; exact Finset.mem_univ r
      rw [Finset.mem_biUnion] at hr
      obtain ⟨j, _, hj⟩ := hr
      exact ⟨j, (Finset.mem_filter.mp hj).2⟩
    have hsum_nb := (occVec54_sum_add_blank_of_valid hn y hvalid).1
    have hk_eq : (nonblankPos54 n K y).card = ∑ i : Fin n, (α i : ℕ) := by
      rw [← hsum_nb]
      exact Finset.sum_congr rfl fun i _ => hocc i
    refine ⟨hvalid, ?_, fun i => (hocc i).symm⟩
    omega
  · rintro ⟨hvalid, hk_ge, hα⟩
    have hboth := occVec54_sum_add_blank_of_valid hn y hvalid
    have hocc : ∀ i : Fin n, occVec54 n K y i = (α i : ℕ) := fun i => (hα i).symm
    have hsum_eq : ∑ i : Fin n, (α i : ℕ) = (nonblankPos54 n K y).card := by
      rw [← hboth.1]
      exact Finset.sum_congr rfl fun i _ => hα i
    refine ⟨hocc, ?_⟩
    rw [hsum_eq]
    exact hboth.2

lemma prod_w_pow_occ_eq_prod_dirAmp {n K : ℕ} (_hn : 1 ≤ n)
    (y : Qubits (2 * K * (Nat.clog 2 n + 1))) (hvalid : allValidSyms54 n K y)
    (w : EuclideanSpace ℝ (Fin n)) :
    ((∏ i : Fin n, w i ^ occVec54 n K y i : ℝ) : ℂ) =
      ∏ r ∈ nonblankPos54 n K y, dirAmp (Nat.clog 2 n + 1) w (splitReg (2 * K) (Nat.clog 2 n + 1) y r) := by
  let s := Nat.clog 2 n + 1
  have hns : n ≤ 2 ^ s := by
    have h1 : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by norm_num : 1 < 2) n
    have h2 : 2 ^ Nat.clog 2 n ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)
    exact h1.trans h2
  let fib : Fin n → Finset (Fin (2 * K)) := fun i =>
    Finset.univ.filter fun r => splitReg (2 * K) s y r = natToBits s i.val
  have hdisj : (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint fib := by
    intro i _ j _ hij
    change Disjoint (fib i) (fib j)
    rw [Finset.disjoint_left]
    intro r hri hrj
    rw [Finset.mem_filter] at hri hrj
    have heq : particleSym54 n s (Fin.castSucc i) = particleSym54 n s (Fin.castSucc j) := by
      simp only [particleSym54, Fin.val_castSucc, i.isLt, j.isLt, ↓reduceIte]
      exact hri.2.symm.trans hrj.2
    have hval : (Fin.castSucc i).val = (Fin.castSucc j).val :=
      congrArg (fun x : Fin (n + 1) => x.val) (particleSym54_inj n heq)
    exact hij (Fin.ext hval)
  have hbi : (Finset.univ : Finset (Fin n)).biUnion fib = nonblankPos54 n K y := by
    ext r
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter,
      nonblankPos54, fib]
    constructor
    · rintro ⟨i, hr⟩
      rw [hr]
      have hmsb := particleSym54_msb n (Fin.castSucc i)
      have hlt : (Fin.castSucc i).val < n := i.isLt
      rw [particleSym54_lt hlt] at hmsb
      simp only [Fin.val_castSucc] at hmsb
      rw [hmsb]
      simp [Nat.ne_of_lt i.isLt]
    · intro hmsb
      obtain ⟨j, hj⟩ := hvalid r
      have hmsb' := particleSym54_msb n j
      rw [← hj, hmsb] at hmsb'
      have hjn : j.val < n := by
        have hne : j.val ≠ n := of_decide_eq_false hmsb'.symm
        omega
      exact ⟨⟨j.val, hjn⟩, by rw [hj, particleSym54_lt hjn]⟩
  rw [← hbi, Finset.prod_biUnion hdisj, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hfib : ∏ r ∈ fib i, dirAmp s w (splitReg (2 * K) s y r) =
      ∏ _r ∈ fib i, ((w i : ℝ) : ℂ) := by
    refine Finset.prod_congr rfl fun r hr => ?_
    rw [(Finset.mem_filter.mp hr).2, dirAmp_natToBits hns w i]
  rw [hfib, Finset.prod_const, Complex.ofReal_pow]
  rfl

/-! ### 3. Wire Decomposition and `measChannelOut` Collapse -/

noncomputable def wireSrcEquiv54 (K s m : ℕ) (partEmb : Fin (2 * K * s) ↪ Fin m) :
    Fin m ≃ (Fin K × Fin s) ⊕ (Fin K × Fin s) ⊕ { a : Fin m // a ∉ Set.range partEmb } where
  toFun a :=
    if h : a ∈ Set.range partEmb then
      let p := finProdFinEquiv.symm (Classical.choose h)
      if hp : p.1.val < K then Sum.inl (⟨p.1.val, hp⟩, p.2)
      else Sum.inr (Sum.inl (⟨p.1.val - K, by omega⟩, p.2))
    else Sum.inr (Sum.inr ⟨a, h⟩)
  invFun
    | Sum.inl (k, j) => partEmb (finProdFinEquiv (⟨k.val, by omega⟩, j))
    | Sum.inr (Sum.inl (k, j)) => partEmb (finProdFinEquiv (⟨K + k.val, by omega⟩, j))
    | Sum.inr (Sum.inr a) => a.1
  left_inv a := by
    by_cases ha : a ∈ Set.range partEmb
    · dsimp only
      rw [dif_pos ha]
      set q := Classical.choose ha
      have hq : partEmb q = a := Classical.choose_spec ha
      set p := finProdFinEquiv.symm q
      split_ifs with hp
      · change partEmb (finProdFinEquiv (⟨p.1.val, by omega⟩, p.2)) = a
        have hp1 : (⟨p.1.val, by omega⟩ : Fin (2 * K)) = p.1 := Fin.ext rfl
        rw [hp1, show (p.1, p.2) = p from Prod.eta p, finProdFinEquiv.apply_symm_apply, hq]
      · change partEmb (finProdFinEquiv (⟨K + (p.1.val - K), by omega⟩, p.2)) = a
        have hge : K ≤ p.1.val := Nat.le_of_not_lt hp
        have hp1 : (⟨K + (p.1.val - K), by omega⟩ : Fin (2 * K)) = p.1 := by
          ext; dsimp; omega
        rw [hp1, show (p.1, p.2) = p from Prod.eta p, finProdFinEquiv.apply_symm_apply, hq]
    · dsimp only
      rw [dif_neg ha]
  right_inv x := by
    rcases x with ⟨k, j⟩ | ⟨k, j⟩ | ⟨a, ha⟩
    · have hex : partEmb (finProdFinEquiv (⟨k.val, by omega⟩, j)) ∈ Set.range partEmb :=
        ⟨finProdFinEquiv (⟨k.val, by omega⟩, j), rfl⟩
      dsimp only
      rw [dif_pos hex]
      have hp_eq : finProdFinEquiv.symm (Classical.choose hex) = (⟨k.val, by omega⟩, j) := by
        rw [partEmb.injective (Classical.choose_spec hex), finProdFinEquiv.symm_apply_apply]
      have hv1 : (finProdFinEquiv.symm (Classical.choose hex)).1.val = k.val :=
        congrArg (fun u => u.1.val) hp_eq
      have hv2 : (finProdFinEquiv.symm (Classical.choose hex)).2 = j :=
        congrArg Prod.snd hp_eq
      split_ifs with hp
      · exact congrArg Sum.inl (Prod.ext (Fin.ext (by dsimp; exact hv1)) hv2)
      · exact absurd (by rw [hv1]; exact k.isLt) hp
    · have hex : partEmb (finProdFinEquiv (⟨K + k.val, by omega⟩, j)) ∈ Set.range partEmb :=
        ⟨finProdFinEquiv (⟨K + k.val, by omega⟩, j), rfl⟩
      dsimp only
      rw [dif_pos hex]
      have hp_eq : finProdFinEquiv.symm (Classical.choose hex) = (⟨K + k.val, by omega⟩, j) := by
        rw [partEmb.injective (Classical.choose_spec hex), finProdFinEquiv.symm_apply_apply]
      have hv1 : (finProdFinEquiv.symm (Classical.choose hex)).1.val = K + k.val :=
        congrArg (fun u => u.1.val) hp_eq
      have hv2 : (finProdFinEquiv.symm (Classical.choose hex)).2 = j :=
        congrArg Prod.snd hp_eq
      split_ifs with hp
      · omega
      · exact congrArg Sum.inr (congrArg Sum.inl (Prod.ext (Fin.ext (by dsimp; omega)) hv2))
    · dsimp only
      rw [dif_neg ha]

lemma wireSrcEquiv54_symm_inl (K s m : ℕ) (partEmb : Fin (2 * K * s) ↪ Fin m) (k : Fin K) (j : Fin s) :
    (wireSrcEquiv54 K s m partEmb).symm (Sum.inl (k, j)) =
      partEmb (finProdFinEquiv (⟨k.val, by omega⟩, j)) := rfl

lemma wireSrcEquiv54_symm_inr_inl (K s m : ℕ) (partEmb : Fin (2 * K * s) ↪ Fin m) (k : Fin K) (j : Fin s) :
    (wireSrcEquiv54 K s m partEmb).symm (Sum.inr (Sum.inl (k, j))) =
      partEmb (finProdFinEquiv (⟨K + k.val, by omega⟩, j)) := rfl

lemma wireSrcEquiv54_symm_inr_inr (K s m : ℕ) (partEmb : Fin (2 * K * s) ↪ Fin m)
    (a : { a : Fin m // a ∉ Set.range partEmb }) :
    (wireSrcEquiv54 K s m partEmb).symm (Sum.inr (Sum.inr a)) = a.1 := rfl

noncomputable def qubitsDecomp54 (K s m : ℕ) (partEmb : Fin (2 * K * s) ↪ Fin m) :
    Qubits m ≃ Qubits (K * s) × (Fin K → Qubits s) × ({ a : Fin m // a ∉ Set.range partEmb } → Bool) where
  toFun z :=
    (flatReg K s fun k j => z (partEmb (finProdFinEquiv (⟨k.val, by omega⟩, j))),
      fun k j => z (partEmb (finProdFinEquiv (⟨K + k.val, by omega⟩, j))),
      fun a => z a.1)
  invFun p a :=
    match wireSrcEquiv54 K s m partEmb a with
    | Sum.inl (k, j) => splitReg K s p.1 k j
    | Sum.inr (Sum.inl (k, j)) => p.2.1 k j
    | Sum.inr (Sum.inr r) => p.2.2 r
  left_inv z := by
    funext a
    dsimp only
    cases h : wireSrcEquiv54 K s m partEmb a with
    | inl kj =>
      have ha : a = partEmb (finProdFinEquiv (⟨kj.1.val, by omega⟩, kj.2)) := by
        rw [← wireSrcEquiv54_symm_inl, ← h, Equiv.symm_apply_apply]
      rw [ha, splitReg_flatReg_54]
    | inr rest =>
      cases rest with
      | inl kj =>
        have ha : a = partEmb (finProdFinEquiv (⟨K + kj.1.val, by omega⟩, kj.2)) := by
          rw [← wireSrcEquiv54_symm_inr_inl, ← h, Equiv.symm_apply_apply]
        rw [ha]
      | inr r =>
        have ha : a = r.1 := by
          rw [← wireSrcEquiv54_symm_inr_inr, ← h, Equiv.symm_apply_apply]
        rw [ha]
  right_inv p := by
    rcases p with ⟨y, g, d⟩
    dsimp only
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext i
      rcases finProdFinEquiv.surjective i with ⟨⟨k, j⟩, rfl⟩
      dsimp only [flatReg]
      rw [finProdFinEquiv.symm_apply_apply]
      have hw : wireSrcEquiv54 K s m partEmb (partEmb (finProdFinEquiv (⟨k.val, by omega⟩, j))) =
          Sum.inl (k, j) := by
        rw [← wireSrcEquiv54_symm_inl, Equiv.apply_symm_apply]
      rw [hw]
      rfl
    · funext k j
      dsimp only
      have hw : wireSrcEquiv54 K s m partEmb (partEmb (finProdFinEquiv (⟨K + k.val, by omega⟩, j))) =
          Sum.inr (Sum.inl (k, j)) := by
        rw [← wireSrcEquiv54_symm_inr_inl, Equiv.apply_symm_apply]
      rw [hw]
    · funext r
      dsimp only
      have hw : wireSrcEquiv54 K s m partEmb r.1 = Sum.inr (Sum.inr r) := by
        rw [← wireSrcEquiv54_symm_inr_inr, Equiv.apply_symm_apply]
      rw [hw]

lemma qubitsDecomp54_out_eq {K s m : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m)
    (out : Fin (K * s) ↪ Fin m)
    (hout : ∀ (k : Fin K) (j : Fin s),
      out (finProdFinEquiv (k, j)) = partEmb (finProdFinEquiv (⟨k.val, by omega⟩, j)))
    (z : Qubits m) :
    z ∘ out = (qubitsDecomp54 K s m partEmb z).1 := by
  funext i
  rcases finProdFinEquiv.surjective i with ⟨⟨k, j⟩, rfl⟩
  simp [qubitsDecomp54, flatReg, hout k j]

lemma qubitsDecomp54_rest_iff {K s m : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m)
    (out : Fin (K * s) ↪ Fin m)
    (hout : ∀ (k : Fin K) (j : Fin s),
      out (finProdFinEquiv (k, j)) = partEmb (finProdFinEquiv (⟨k.val, by omega⟩, j)))
    (z z' : Qubits m) :
    (∀ a : Fin m, (∀ i : Fin (K * s), out i ≠ a) → z a = z' a) ↔
      (qubitsDecomp54 K s m partEmb z).2 = (qubitsDecomp54 K s m partEmb z').2 := by
  constructor
  · intro h
    refine Prod.ext (funext fun k => funext fun j => ?_) (funext fun a => ?_)
    · exact h _ fun i hi => by
        rcases finProdFinEquiv.surjective i with ⟨⟨k', j'⟩, rfl⟩
        rw [hout] at hi
        have heq := finProdFinEquiv.injective (partEmb.injective hi)
        have hv := congrArg Fin.val (congrArg Prod.fst heq)
        dsimp at hv
        omega
    · exact h _ fun i hi => by
        rcases finProdFinEquiv.surjective i with ⟨⟨k', j'⟩, rfl⟩
        rw [hout] at hi
        exact absurd ⟨_, hi⟩ a.2
  · intro h a ha
    cases hw : wireSrcEquiv54 K s m partEmb a with
    | inl kj =>
      have ha' : a = partEmb (finProdFinEquiv (⟨kj.1.val, by omega⟩, kj.2)) := by
        rw [← wireSrcEquiv54_symm_inl, ← hw, Equiv.symm_apply_apply]
      exfalso
      exact ha (finProdFinEquiv kj) (by rw [hout, ha'])
    | inr rest =>
      cases rest with
      | inl kj =>
        have ha' : a = partEmb (finProdFinEquiv (⟨K + kj.1.val, by omega⟩, kj.2)) := by
          rw [← wireSrcEquiv54_symm_inr_inl, ← hw, Equiv.symm_apply_apply]
        have h21 := congrFun (congrFun (congrArg Prod.fst h) kj.1) kj.2
        simpa [qubitsDecomp54, ha'] using h21
      | inr r =>
        have ha' : a = r.1 := by
          rw [← wireSrcEquiv54_symm_inr_inr, ← hw, Equiv.symm_apply_apply]
        have h22 := congrFun (congrArg Prod.snd h) r
        simpa [qubitsDecomp54, ha'] using h22

lemma choose_mul_factorial_eq {N k : ℕ} (hk : k ≤ N) :
    ((k.factorial : ℝ) * ((N - k).factorial : ℝ)) / ((N.factorial : ℝ)) =
      ((Nat.choose N k : ℝ))⁻¹ := by
  have hnat : k.factorial * (N - k).factorial * Nat.choose N k = N.factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial hk
    linarith
  have hN_pos : (0 : ℝ) < N.factorial := Nat.cast_pos.mpr (Nat.factorial_pos N)
  have hch_pos : (0 : ℝ) < Nat.choose N k := Nat.cast_pos.mpr (Nat.choose_pos hk)
  have hreal : (k.factorial : ℝ) * ((N - k).factorial : ℝ) * (Nat.choose N k : ℝ) = (N.factorial : ℝ) := by
    exact_mod_cast hnat
  rw [div_eq_inv_mul, eq_comm, inv_eq_iff_eq_inv]
  field_simp
  linarith

lemma card_qubits_filter_false_eq_choose (N k : ℕ) :
    (Finset.univ.filter fun t : Qubits N => (Finset.univ.filter fun j => t j = false).card = k).card =
      Nat.choose N k := by
  let S : Finset (Finset (Fin N)) := Finset.univ.powersetCard k
  have hcard : S.card = Nat.choose N k := by
    simp [S, Finset.card_powersetCard]
  rw [← hcard]
  refine Finset.card_bij (fun t _ => Finset.univ.filter fun j => t j = false) ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_filter] at ht
    simp [S, Finset.mem_powersetCard, ht.2]
  · intro t₁ _ t₂ _ heq
    funext j
    have hj : (j ∈ Finset.univ.filter fun r => t₁ r = false) ↔
        (j ∈ Finset.univ.filter fun r => t₂ r = false) := by rw [heq]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    cases h1 : t₁ j <;> cases h2 : t₂ j <;> simp_all
  · intro A hA
    rw [Finset.mem_powersetCard] at hA
    refine ⟨fun j => decide (j ∉ A), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hflt : (Finset.univ.filter fun j : Fin N => decide (j ∉ A) = false) = A := by
        ext j; simp
      rw [hflt]
      exact hA.2
    · ext j; simp

theorem band_channel_algebra_54_aux
    (coeff1D : ℕ → ℝ)
    (hermCoeff_formula : ∀ {n : ℕ}, 1 ≤ n → ∀ (w : EuclideanSpace ℝ (Fin n)), ‖w‖ = 1 →
      ∀ α : Fin n → ℕ, hermCoeff w α =
        coeff1D (∑ i, α i) *
          Real.sqrt (((∑ i, α i).factorial : ℝ) / ∏ i, ((α i).factorial : ℝ)) *
          ∏ i, w i ^ α i)
    (p1D53_eq_sum : ∀ K : ℕ, p1D53 K = ∑ k ∈ Finset.Icc K (2 * K), (coeff1D k) ^ 2)
    (n K D q e : ℕ) (hn : 1 ≤ n) (hK : 1 ≤ K) (_hKD : 2 * K + 1 ≤ D) (_hDq : D ≤ 2 ^ q) :
    let s := Nat.clog 2 n + 1
    ∀ (partEmb : Fin (2 * K * s) ↪ Fin (n * q + e))
      (meas : Fin (2 * K) ↪ Fin (n * q + e))
      (out : Fin (K * s) ↪ Fin (n * q + e))
      (V : Matrix (Qubits (n * q + e)) (Qubits (n * q + e)) ℂ)
      (W : Qubits (2 * K) → Matrix (Qubits (n * q + e)) (Qubits (n * q + e)) ℂ)
      (degState : ℕ → Qubits (n * q + e)),
      (∀ j : Fin (2 * K), meas j = partEmb (finProdFinEquiv (j, ⟨0, Nat.succ_pos _⟩))) →
      (∀ (k : Fin K) (j : Fin s),
        out (finProdFinEquiv (k, j)) = partEmb (finProdFinEquiv (⟨k.val, by omega⟩, j))) →
      (∀ (α : Fin n → ℕ) (hk : K ≤ ∑ i, α i ∧ ∑ i, α i ≤ 2 * K),
        act V (padKet e (ket (flatReg n q fun i => natToBits q (α i)))) =
          embedPartAndDeg54 partEmb (multinomKet54 n s K α hk) (degState (∑ i, α i))) →
      (∀ t : Qubits (2 * K), K ≤ (Finset.univ.filter fun j => t j = false).card →
        ∃ σ : Equiv.Perm (Fin (2 * K)),
          (∀ k : Fin K, t (σ ⟨k.val, by omega⟩) = false) ∧
          ∀ x : Qubits (n * q + e),
            act (W t) (ket x) = ket (permPartReg54 partEmb σ x)) →
      ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
        measChannelOut V W meas out (padKet e (bandKet n q K w)) = dirTensorPow s K w := by
  intro s partEmb meas out V W degState hmeas hout hV hW w hw
  classical
  obtain ⟨c_band, hc_pos, h1D, hbw⟩ := hermite_band_bounds_53.1
  have hbw_pos : 0 < bandWeight w K := by
    rw [hbw n K w hw]
    have hK_pos : (0 : ℝ) < K := by exact_mod_cast hK
    have hpos : 0 < c_band / Real.sqrt K := by positivity
    exact hpos.trans_le (h1D K hK).1
  have hbw_eq : bandWeight w K = ∑ k ∈ Finset.Icc K (2 * K), (coeff1D k) ^ 2 := by
    rw [hbw n K w hw, p1D53_eq_sum K]
  have hns : n ≤ 2 ^ s := by
    have h1 : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by norm_num : 1 < 2) n
    have h2 : 2 ^ Nat.clog 2 n ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)
    exact h1.trans h2
  have hVψ : ∀ z : Qubits (n * q + e),
      (act V (padKet e (bandKet n q K w))) z =
        let y : Qubits (2 * K * s) := fun i => z (partEmb i)
        let k := (nonblankPos54 n K y).card
        if hk : K ≤ k ∧ k ≤ 2 * K then
          if allValidSyms54 n K y ∧ (∀ a : Fin (n * q + e), a ∉ Set.range partEmb → z a = degState k a) then
            ((coeff1D k / Real.sqrt (bandWeight w K) : ℝ) : ℂ) *
              ((Real.sqrt ((Nat.choose (2 * K) k : ℝ)⁻¹) : ℝ) : ℂ) *
              ∏ r ∈ nonblankPos54 n K y, dirAmp s w (splitReg (2 * K) s y r)
          else 0
        else 0 := by
    intro z
    rw [padKet_bandKet_eq_sum, act_sum, WithLp.ofLp_sum, Finset.sum_apply]
    have hterm : ∀ α : Fin n → Fin (2 * K + 1),
        (act V (if K ≤ ∑ i, (α i : ℕ) ∧ ∑ i, (α i : ℕ) ≤ 2 * K then
          ((hermCoeff w (fun i => (α i : ℕ)) / Real.sqrt (bandWeight w K) : ℝ) : ℂ) •
            padKet e (ket (flatReg n q fun i => natToBits q (α i)))
          else 0)) z =
          if hkα : K ≤ ∑ i, (α i : ℕ) ∧ ∑ i, (α i : ℕ) ≤ 2 * K then
            ((hermCoeff w (fun i => (α i : ℕ)) / Real.sqrt (bandWeight w K) : ℝ) : ℂ) *
              (embedPartAndDeg54 partEmb
                (multinomKet54 n s K (fun i => (α i : ℕ)) hkα)
                (degState (∑ i, (α i : ℕ)))) z
          else 0 := by
      intro α
      split_ifs with hkα
      · rw [act_smul, hV (fun i => (α i : ℕ)) hkα, PiLp.smul_apply, smul_eq_mul]
      · simp [act]
    simp_rw [hterm]
    let y : Qubits (2 * K * s) := fun i => z (partEmb i)
    let k := (nonblankPos54 n K y).card
    have hk_le : k ≤ 2 * K := by
      simpa [k, nonblankPos54] using Finset.card_filter_le (Finset.univ : Finset (Fin (2 * K))) _
    by_cases hcond : K ≤ k ∧ allValidSyms54 n K y ∧
        (∀ a : Fin (n * q + e), a ∉ Set.range partEmb → z a = degState k a)
    · rcases hcond with ⟨hk_ge, hvalid, hdeg⟩
      have hk : K ≤ k ∧ k ≤ 2 * K := ⟨hk_ge, hk_le⟩
      rw [dif_pos hk, if_pos ⟨hvalid, hdeg⟩]
      have hocc_lt : ∀ i : Fin n, occVec54 n K y i < 2 * K + 1 := fun i => by
        have hsub : occVec54 n K y i ≤ ∑ j : Fin n, occVec54 n K y j :=
          Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        have hsum_nb := (occVec54_sum_add_blank_of_valid hn y hvalid).1
        omega
      let α₀ : Fin n → Fin (2 * K + 1) := fun i => ⟨occVec54 n K y i, hocc_lt i⟩
      have hkα₀ : K ≤ ∑ i, (α₀ i : ℕ) ∧ ∑ i, (α₀ i : ℕ) ≤ 2 * K := by
        have hsum_nb := (occVec54_sum_add_blank_of_valid hn y hvalid).1
        change K ≤ ∑ i, occVec54 n K y i ∧ ∑ i, occVec54 n K y i ≤ 2 * K
        rw [hsum_nb]
        exact hk
      rw [Finset.sum_eq_single α₀]
      · rw [dif_pos hkα₀]
        have hsum_eq : ∑ i : Fin n, (α₀ i : ℕ) = k :=
          (occVec54_sum_add_blank_of_valid hn y hvalid).1
        have hdeg' : ∀ a : Fin (n * q + e), a ∉ Set.range partEmb → z a = degState (∑ i, (α₀ i : ℕ)) a := by
          simpa [hsum_eq] using hdeg
        rw [embedPartAndDeg54_apply, if_pos hdeg']
        have hcond_α₀ : (∀ i : Fin n,
              (Finset.univ.filter fun r : Fin (2 * K) => splitReg (2 * K) s y r = natToBits s i.val).card =
                (α₀ i : ℕ)) ∧
            (Finset.univ.filter fun r : Fin (2 * K) => splitReg (2 * K) s y r = blankSym54 s).card =
              2 * K - ∑ i : Fin n, (α₀ i : ℕ) := by
          have hcond_iff := (multinomKet54_cond_iff hn y α₀ hkα₀).mpr ⟨hvalid, hk_ge, fun _ => rfl⟩
          exact hcond_iff
        change ((hermCoeff w (fun i => (α₀ i : ℕ)) / Real.sqrt (bandWeight w K) : ℝ) : ℂ) *
            ((multinomKet54 n s K (fun i => (α₀ i : ℕ)) hkα₀) y) = _
        simp only [multinomKet54, if_pos hcond_α₀]
        rw [hermCoeff_formula hn w hw (fun i => (α₀ i : ℕ)), hsum_eq]
        have hprod_pos : (0 : ℝ) < ∏ i : Fin n, (((α₀ i : ℕ).factorial) : ℝ) :=
          Finset.prod_pos fun i _ => Nat.cast_pos.mpr (Nat.factorial_pos _)
        have hk_fac_pos : (0 : ℝ) ≤ (k.factorial : ℝ) := Nat.cast_nonneg _
        have h2Kk_fac_pos : (0 : ℝ) ≤ ((2 * K - k).factorial : ℝ) := Nat.cast_nonneg _
        have h2K_fac_pos : (0 : ℝ) ≤ ((2 * K).factorial : ℝ) := Nat.cast_nonneg _
        have hsqrt_cancel :
            Real.sqrt ((k.factorial : ℝ) / ∏ i : Fin n, (((α₀ i : ℕ).factorial) : ℝ)) *
              Real.sqrt ((∏ i : Fin n, (((α₀ i : ℕ).factorial) : ℝ)) *
                ((2 * K - k).factorial : ℝ) / ((2 * K).factorial : ℝ)) =
              Real.sqrt ((Nat.choose (2 * K) k : ℝ)⁻¹) := by
          rw [← Real.sqrt_mul (div_nonneg hk_fac_pos hprod_pos.le)]
          have halg : ((k.factorial : ℝ) / ∏ i : Fin n, (((α₀ i : ℕ).factorial) : ℝ)) *
              ((∏ i : Fin n, (((α₀ i : ℕ).factorial) : ℝ)) * ((2 * K - k).factorial : ℝ) /
                ((2 * K).factorial : ℝ)) =
              ((k.factorial : ℝ) * ((2 * K - k).factorial : ℝ)) / ((2 * K).factorial : ℝ) := by
            field_simp [hprod_pos.ne']
          rw [halg, choose_mul_factorial_eq hk_le]
        have hpow_w := prod_w_pow_occ_eq_prod_dirAmp hn y hvalid w
        rw [← Complex.ofReal_mul, show (coeff1D k *
              Real.sqrt ((k.factorial : ℝ) / ∏ i : Fin n, (((α₀ i : ℕ).factorial) : ℝ)) *
              ∏ i : Fin n, w i ^ (α₀ i : ℕ)) / Real.sqrt (bandWeight w K) *
              Real.sqrt ((∏ i : Fin n, (((α₀ i : ℕ).factorial) : ℝ)) *
                ((2 * K - k).factorial : ℝ) / ((2 * K).factorial : ℝ)) =
            (coeff1D k / Real.sqrt (bandWeight w K)) *
              (Real.sqrt ((k.factorial : ℝ) / ∏ i : Fin n, (((α₀ i : ℕ).factorial) : ℝ)) *
                Real.sqrt ((∏ i : Fin n, (((α₀ i : ℕ).factorial) : ℝ)) *
                  ((2 * K - k).factorial : ℝ) / ((2 * K).factorial : ℝ))) *
              ∏ i : Fin n, w i ^ (α₀ i : ℕ) by ring]
        rw [hsqrt_cancel, Complex.ofReal_mul, Complex.ofReal_mul]
        have hpow_w' : ((∏ i : Fin n, w i ^ (α₀ i : ℕ) : ℝ) : ℂ) =
            ∏ r ∈ nonblankPos54 n K y, dirAmp s w (splitReg (2 * K) s y r) := by
          simpa [α₀] using hpow_w
        rw [hpow_w']
      · intro α _ hne
        split_ifs with hkα
        · rw [embedPartAndDeg54_apply]
          split_ifs with hdegα
          · simp only [multinomKet54]
            split_ifs with hmα
            · exfalso
              have hiff := (multinomKet54_cond_iff hn y α hkα).mp hmα
              apply hne
              ext i
              exact (hiff.2.2 i)
            · simp
          · simp
        · rfl
      · intro hnot; exact absurd (Finset.mem_univ α₀) hnot
    · have hzero_rhs : (if hk : K ≤ k ∧ k ≤ 2 * K then
            if allValidSyms54 n K y ∧ (∀ a : Fin (n * q + e), a ∉ Set.range partEmb → z a = degState k a) then
              ((coeff1D k / Real.sqrt (bandWeight w K) : ℝ) : ℂ) *
                ((Real.sqrt ((Nat.choose (2 * K) k : ℝ)⁻¹) : ℝ) : ℂ) *
                ∏ r ∈ nonblankPos54 n K y, dirAmp s w (splitReg (2 * K) s y r)
            else 0 else 0) = 0 := by
        split_ifs with hk h2
        · exfalso; exact hcond ⟨hk.1, h2.1, h2.2⟩
        · rfl
        · rfl
      rw [hzero_rhs]
      refine Finset.sum_eq_zero fun α _ => ?_
      split_ifs with hkα
      · rw [embedPartAndDeg54_apply]
        split_ifs with hdegα
        · simp only [multinomKet54]
          split_ifs with hmα
          · exfalso
            have hiff := (multinomKet54_cond_iff hn y α hkα).mp hmα
            have hsum_eq : ∑ i : Fin n, (α i : ℕ) = k := by
              change ∑ i : Fin n, (α i : ℕ) = (nonblankPos54 n K y).card
              rw [← (occVec54_sum_add_blank_of_valid hn y hiff.1).1]
              exact Finset.sum_congr rfl fun i _ => hiff.2.2 i
            rw [hsum_eq] at hdegα
            exact hcond ⟨hiff.2.1, hiff.1, hdegα⟩
          · simp
        · simp
      · rfl
  -- Now evaluate `measChannelOut`
  ext y y'
  unfold measChannelOut
  rw [Matrix.of_apply]
  let φ : Qubits (2 * K) → Qubits (n * q + e) → ℂ := fun t =>
    Matrix.mulVec (W t) (fun z => if z ∘ meas = t then (act V (padKet e (bandKet n q K w))) z else 0)
  change ∑ t : Qubits (2 * K), ∑ z : Qubits (n * q + e), ∑ z' : Qubits (n * q + e),
      (if z ∘ out = y ∧ z' ∘ out = y' ∧ ∀ j : Fin (n * q + e), (∀ i : Fin (K * s), out i ≠ j) → z j = z' j then
        φ t z * conj (φ t z') else 0) =
    dirTensorPow s K w y y'
  have hφ_lt : ∀ t : Qubits (2 * K), (Finset.univ.filter fun j => t j = false).card < K →
      ∀ z : Qubits (n * q + e), φ t z = 0 := by
    intro t ht z
    dsimp only [φ, Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun x _ => ?_
    split_ifs with hxt
    · have hx_nb : (nonblankPos54 n K (fun i => x (partEmb i))).card =
          (Finset.univ.filter fun j => t j = false).card := by
        unfold nonblankPos54
        congr 1
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hmr : splitReg (2 * K) (Nat.clog 2 n + 1) (fun i => x (partEmb i)) r
            ⟨0, Nat.succ_pos _⟩ = x (meas r) := by
          change x (partEmb (finProdFinEquiv (r, ⟨0, Nat.succ_pos _⟩))) = x (meas r)
          rw [hmeas r]
        rw [hmr, ← hxt]
        rfl
      rw [hVψ x]
      dsimp only
      rw [hx_nb]
      have hnot : ¬ (K ≤ (Finset.univ.filter fun j => t j = false).card ∧
          (Finset.univ.filter fun j => t j = false).card ≤ 2 * K) := by omega
      rw [dif_neg hnot, mul_zero]
    · simp
  have hφ_ge : ∀ (t : Qubits (2 * K)) (ht : K ≤ (Finset.univ.filter fun j => t j = false).card),
      ∃ σ : Equiv.Perm (Fin (2 * K)),
        (∀ k : Fin K, t (σ ⟨k.val, by omega⟩) = false) ∧
        ∀ z : Qubits (n * q + e),
          let k_t := (Finset.univ.filter fun j => t j = false).card
          φ t z =
            if (∀ a : Fin (n * q + e), a ∉ Set.range partEmb → z a = degState k_t a) then
              ((coeff1D k_t / Real.sqrt (bandWeight w K) : ℝ) : ℂ) *
                ((Real.sqrt ((Nat.choose (2 * K) k_t : ℝ)⁻¹) : ℝ) : ℂ) *
                ∏ r : Fin (2 * K),
                  if t (σ r) = false then dirAmp s w (splitReg (2 * K) s (fun i => z (partEmb i)) r)
                  else if splitReg (2 * K) s (fun i => z (partEmb i)) r = blankSym54 s then 1 else 0
            else 0 := by
    intro t ht
    obtain ⟨σ, hσ_false, hσ_act⟩ := hW t ht
    refine ⟨σ, hσ_false, fun z => ?_⟩
    dsimp only [φ, Matrix.mulVec, dotProduct]
    let x₀ := permPartReg54 partEmb σ.symm z
    have hW_entry : ∀ x : Qubits (n * q + e), W t z x = if x = x₀ then 1 else 0 := by
      intro x
      have h1 : W t z x = (act (W t) (ket x)) z := by
        change W t z x = ∑ y : Qubits (n * q + e), W t z y * (ket x) y
        simp only [ket, PiLp.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, ↓reduceIte]
      rw [h1, hσ_act x]
      simp only [ket, PiLp.single_apply]
      by_cases hx : x = x₀
      · subst hx
        rw [if_pos rfl, if_pos (permPartReg54_apply_symm partEmb σ z).symm]
      · rw [if_neg hx]
        refine if_neg fun h => hx ?_
        have := congrArg (permPartReg54 partEmb σ.symm) h
        rw [permPartReg54_symm_apply] at this
        exact this.symm
    rw [Finset.sum_eq_single x₀]
    · rw [hW_entry x₀, if_pos rfl, one_mul]
      let k_t := (Finset.univ.filter fun j => t j = false).card
      have hk_t : K ≤ k_t ∧ k_t ≤ 2 * K :=
        ⟨ht, by simpa [k_t] using Finset.card_filter_le (Finset.univ : Finset (Fin (2 * K))) _⟩
      have hx₀_off : (∀ a : Fin (n * q + e), a ∉ Set.range partEmb → x₀ a = degState k_t a) ↔
          (∀ a : Fin (n * q + e), a ∉ Set.range partEmb → z a = degState k_t a) := by
        refine forall₂_congr fun a ha => ?_
        simp [x₀, permPartReg54_off partEmb σ.symm z ha]
      have hx₀_reg : ∀ r : Fin (2 * K),
          splitReg (2 * K) s (fun i => x₀ (partEmb i)) r =
            splitReg (2 * K) s (fun i => z (partEmb i)) (σ.symm r) := by
        intro r
        funext b
        change x₀ (partEmb (finProdFinEquiv (r, b))) = z (partEmb (finProdFinEquiv (σ.symm r, b)))
        exact permPartReg54_part partEmb σ.symm z r b
      have hx₀_meas : (x₀ ∘ meas = t) ↔
          ∀ r : Fin (2 * K),
            (splitReg (2 * K) s (fun i => z (partEmb i)) r) ⟨0, Nat.succ_pos _⟩ = t (σ r) := by
        constructor
        · intro h r
          have h1 := congrFun h (σ r)
          simp only [Function.comp_apply, hmeas (σ r)] at h1
          have h2 : x₀ (partEmb (finProdFinEquiv (σ r, ⟨0, Nat.succ_pos _⟩))) =
              z (partEmb (finProdFinEquiv (r, ⟨0, Nat.succ_pos _⟩))) := by
            change permPartReg54 partEmb σ.symm z (partEmb (finProdFinEquiv (σ r, ⟨0, Nat.succ_pos _⟩))) = _
            rw [permPartReg54_part, Equiv.symm_apply_apply]
          change splitReg (2 * K) s (fun i => z (partEmb i)) r ⟨0, Nat.succ_pos _⟩ = t (σ r)
          change z (partEmb (finProdFinEquiv (r, ⟨0, Nat.succ_pos _⟩))) = t (σ r)
          rw [← h2]; exact h1
        · intro h
          funext j
          simp only [Function.comp_apply, hmeas j]
          have h2 : x₀ (partEmb (finProdFinEquiv (j, ⟨0, Nat.succ_pos _⟩))) =
              z (partEmb (finProdFinEquiv (σ.symm j, ⟨0, Nat.succ_pos _⟩))) :=
            permPartReg54_part partEmb σ.symm z j ⟨0, Nat.succ_pos _⟩
          have h3 : splitReg (2 * K) s (fun i => z (partEmb i)) (σ.symm j) ⟨0, Nat.succ_pos _⟩ =
              t (σ (σ.symm j)) := h (σ.symm j)
          change z (partEmb (finProdFinEquiv (σ.symm j, ⟨0, Nat.succ_pos _⟩))) = t (σ (σ.symm j)) at h3
          rw [h2, h3, Equiv.apply_symm_apply]
      have hx₀_valid : allValidSyms54 n K (fun i => x₀ (partEmb i)) ↔
          allValidSyms54 n K (fun i => z (partEmb i)) := by
        constructor
        · intro h r
          obtain ⟨j, hj⟩ := h (σ r)
          rw [hx₀_reg, Equiv.symm_apply_apply] at hj
          exact ⟨j, hj⟩
        · intro h r
          obtain ⟨j, hj⟩ := h (σ.symm r)
          rw [hx₀_reg]
          exact ⟨j, hj⟩
      by_cases hdeg_z : ∀ a : Fin (n * q + e), a ∉ Set.range partEmb → z a = degState k_t a
      · rw [if_pos hdeg_z]
        by_cases hmeas_z : x₀ ∘ meas = t
        · rw [if_pos hmeas_z, hVψ x₀]
          dsimp only
          have hx₀_nb : (nonblankPos54 n K (fun i => x₀ (partEmb i))).card = k_t := by
            unfold nonblankPos54
            congr 1
            ext r
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            have h1 : (splitReg (2 * K) (Nat.clog 2 n + 1) (fun i => x₀ (partEmb i)) r) ⟨0, Nat.succ_pos _⟩ =
                x₀ (meas r) := by
              change x₀ (partEmb (finProdFinEquiv (r, ⟨0, Nat.succ_pos _⟩))) = x₀ (meas r)
              rw [hmeas r]
            have hr' : x₀ (meas r) = t r := congrFun hmeas_z r
            rw [h1, hr']
          rw [hx₀_nb, dif_pos hk_t]
          by_cases hval_z : allValidSyms54 n K (fun i => z (partEmb i))
          · have hval_x₀ : allValidSyms54 n K (fun i => x₀ (partEmb i)) := hx₀_valid.mpr hval_z
            have hdeg_x₀ : ∀ a : Fin (n * q + e), a ∉ Set.range partEmb → x₀ a = degState k_t a :=
              hx₀_off.mpr hdeg_z
            rw [if_pos ⟨hval_x₀, hdeg_x₀⟩]
            congr 1
            have hprod_eq : ∏ r ∈ nonblankPos54 n K (fun i => x₀ (partEmb i)),
                dirAmp s w (splitReg (2 * K) s (fun i => x₀ (partEmb i)) r) =
                ∏ r : Fin (2 * K),
                  if t (σ r) = false then dirAmp s w (splitReg (2 * K) s (fun i => z (partEmb i)) r)
                  else if splitReg (2 * K) s (fun i => z (partEmb i)) r = blankSym54 s then 1 else 0 := by
              have h1 : ∏ r ∈ nonblankPos54 n K (fun i => x₀ (partEmb i)),
                    dirAmp s w (splitReg (2 * K) s (fun i => x₀ (partEmb i)) r) =
                  ∏ r : Fin (2 * K),
                    if r ∈ nonblankPos54 n K (fun i => x₀ (partEmb i)) then
                      dirAmp s w (splitReg (2 * K) s (fun i => x₀ (partEmb i)) r)
                    else 1 := by
                rw [← Finset.prod_filter]
                refine Finset.prod_congr (by ext; simp) fun _ _ => rfl
              rw [h1]
              refine Fintype.prod_equiv σ.symm _ _ fun r => ?_
              have hmem : (r ∈ nonblankPos54 n K (fun i => x₀ (partEmb i))) ↔ t r = false := by
                simp only [nonblankPos54, Finset.mem_filter, Finset.mem_univ, true_and]
                have hm : (splitReg (2 * K) (Nat.clog 2 n + 1) (fun i => x₀ (partEmb i)) r) ⟨0, Nat.succ_pos _⟩ =
                    x₀ (meas r) := by
                  change x₀ (partEmb (finProdFinEquiv (r, ⟨0, Nat.succ_pos _⟩))) = x₀ (meas r)
                  rw [hmeas r]
                have hr' : x₀ (meas r) = t r := congrFun hmeas_z r
                rw [hm, hr']
              rw [hx₀_reg r, Equiv.apply_symm_apply]
              by_cases htr : t r = false
              · have hmem' : r ∈ nonblankPos54 n K (fun i => x₀ (partEmb i)) := hmem.mpr htr
                rw [if_pos hmem', if_pos htr]
              · have hnot : r ∉ nonblankPos54 n K (fun i => x₀ (partEmb i)) := by rw [hmem]; exact htr
                rw [if_neg hnot, if_neg htr]
                obtain ⟨j, hj⟩ := hval_z (σ.symm r)
                have hmsb := particleSym54_msb n j
                rw [← hj] at hmsb
                have hmsbz := hx₀_meas.mp hmeas_z (σ.symm r)
                rw [Equiv.apply_symm_apply] at hmsbz
                have htr_true : t r = true := Bool.eq_true_of_not_eq_false htr
                rw [hmsbz, htr_true] at hmsb
                have hjn : j = Fin.last n := Fin.ext (of_decide_eq_true hmsb.symm)
                rw [hj, hjn, particleSym54_last, if_pos rfl]
            exact hprod_eq
          · have hval_x₀ : ¬ allValidSyms54 n K (fun i => x₀ (partEmb i)) := fun h => hval_z (hx₀_valid.mp h)
            rw [if_neg (fun h => hval_x₀ h.1)]
            symm
            have : ∃ r : Fin (2 * K),
                (if t (σ r) = false then dirAmp s w (splitReg (2 * K) s (fun i => z (partEmb i)) r)
                 else if splitReg (2 * K) s (fun i => z (partEmb i)) r = blankSym54 s then (1 : ℂ) else 0) = 0 := by
              by_contra hnone
              push Not at hnone
              apply hval_z
              intro r
              have hr := hnone r
              split_ifs at hr with htr hblank
              · have hnot0 : ∃ i : Fin n, splitReg (2 * K) s (fun i => z (partEmb i)) r = natToBits s i.val := by
                  by_contra hno
                  push Not at hno
                  exact hr (dirAmp_of_notMem w hno)
                obtain ⟨i, hi⟩ := hnot0
                exact ⟨Fin.castSucc i, by rw [hi, particleSym54_lt i.isLt]; rfl⟩
              · exact ⟨Fin.last n, by rw [hblank, particleSym54_last]⟩
              · exact absurd rfl hr
            obtain ⟨r, hr⟩ := this
            rw [Finset.prod_eq_zero (Finset.mem_univ r) hr, mul_zero]
        · rw [if_neg hmeas_z]
          symm
          have hex : ∃ r : Fin (2 * K),
              (splitReg (2 * K) s (fun i => z (partEmb i)) r) ⟨0, Nat.succ_pos _⟩ ≠ t (σ r) := by
            by_contra hall
            push Not at hall
            exact hmeas_z (hx₀_meas.mpr hall)
          obtain ⟨r, hr⟩ := hex
          have hterm0 : (if t (σ r) = false then dirAmp s w (splitReg (2 * K) s (fun i => z (partEmb i)) r)
              else if splitReg (2 * K) s (fun i => z (partEmb i)) r = blankSym54 s then (1 : ℂ) else 0) = 0 := by
            split_ifs with htr hblank
            · apply dirAmp_of_notMem w
              intro i hi
              have hmsb := particleSym54_msb n (Fin.castSucc i)
              rw [particleSym54_lt i.isLt] at hmsb
              simp only [Fin.val_castSucc] at hmsb
              rw [hi, hmsb] at hr
              exact hr (by simp [htr, Nat.ne_of_lt i.isLt])
            · have hmsb := particleSym54_msb n (Fin.last n)
              rw [particleSym54_last] at hmsb
              rw [hblank, hmsb] at hr
              exact absurd (by simp [Bool.eq_true_of_not_eq_false htr]) hr
            · rfl
          rw [Finset.prod_eq_zero (Finset.mem_univ r) hterm0, mul_zero]
      · rw [if_neg hdeg_z]
        split_ifs with hmeas_z
        · rw [hVψ x₀]
          dsimp only
          have hx₀_nb : (nonblankPos54 n K (fun i => x₀ (partEmb i))).card = k_t := by
            unfold nonblankPos54
            congr 1
            ext r
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            have h1 : (splitReg (2 * K) (Nat.clog 2 n + 1) (fun i => x₀ (partEmb i)) r) ⟨0, Nat.succ_pos _⟩ =
                x₀ (meas r) := by
              change x₀ (partEmb (finProdFinEquiv (r, ⟨0, Nat.succ_pos _⟩))) = x₀ (meas r)
              rw [hmeas r]
            have hr' : x₀ (meas r) = t r := congrFun hmeas_z r
            rw [h1, hr']
          rw [hx₀_nb, dif_pos hk_t, if_neg (fun h => hdeg_z (hx₀_off.mp h.2))]
        · rfl
    · intro x _ hxne
      rw [hW_entry x, if_neg hxne, zero_mul]
    · intro hnot; exact absurd (Finset.mem_univ x₀) hnot
  -- Sum over `t`, collapsing `(z, z')` via `qubitsDecomp54`
  have hsum_t : ∀ t : Qubits (2 * K),
      (∑ z : Qubits (n * q + e), ∑ z' : Qubits (n * q + e),
        if z ∘ out = y ∧ z' ∘ out = y' ∧ ∀ j : Fin (n * q + e), (∀ i : Fin (K * s), out i ≠ j) → z j = z' j then
          φ t z * conj (φ t z')
        else 0) =
      let k_t := (Finset.univ.filter fun j => t j = false).card
      if K ≤ k_t then
        (((coeff1D k_t) ^ 2 / (bandWeight w K * Nat.choose (2 * K) k_t) : ℝ) : ℂ) *
          dirTensorPow s K w y y'
      else 0 := by
    intro t
    by_cases ht : K ≤ (Finset.univ.filter fun j => t j = false).card
    · rw [if_pos ht]
      obtain ⟨σ, hσ_false, hφ⟩ := hφ_ge t ht
      let k_t := (Finset.univ.filter fun j => t j = false).card
      have hk_le : k_t ≤ 2 * K := by
        simpa [k_t] using Finset.card_filter_le (Finset.univ : Finset (Fin (2 * K))) _
      let E := qubitsDecomp54 K s (n * q + e) partEmb
      let coeff_t : ℂ := ((coeff1D k_t / Real.sqrt (bandWeight w K) : ℝ) : ℂ) *
        ((Real.sqrt ((Nat.choose (2 * K) k_t : ℝ)⁻¹) : ℝ) : ℂ)
      let tailF : Fin K → Qubits s → ℂ := fun k b =>
        if t (σ ⟨K + k.val, by omega⟩) = false then dirAmp s w b
        else if b = blankSym54 s then 1 else 0
      have hφ_decomp : ∀ (y₀ : Qubits (K * s)) (g : Fin K → Qubits s)
          (d : { a : Fin (n * q + e) // a ∉ Set.range partEmb } → Bool),
          φ t (E.symm (y₀, g, d)) =
            if d = (fun a => degState k_t a.1) then
              coeff_t * (∏ k : Fin K, dirAmp s w (splitReg K s y₀ k)) * ∏ k : Fin K, tailF k (g k)
            else 0 := by
        intro y₀ g d
        rw [hφ]
        have hdeg_iff : (∀ a : Fin (n * q + e), a ∉ Set.range partEmb → E.symm (y₀, g, d) a = degState k_t a) ↔
            d = (fun a => degState k_t a.1) := by
          constructor
          · intro h
            ext ⟨a, ha⟩
            have h1 := h a ha
            have h2 : E.symm (y₀, g, d) a = d ⟨a, ha⟩ := by
              have he := congrArg (fun p => p.2.2 ⟨a, ha⟩) (E.apply_symm_apply (y₀, g, d))
              simpa [E, qubitsDecomp54] using he
            rw [← h2]; exact h1
          · intro hd a ha
            have h2 : E.symm (y₀, g, d) a = d ⟨a, ha⟩ := by
              have he := congrArg (fun p => p.2.2 ⟨a, ha⟩) (E.apply_symm_apply (y₀, g, d))
              simpa [E, qubitsDecomp54] using he
            rw [h2, hd]
        by_cases hd : d = fun a => degState k_t a.1
        · rw [if_pos (hdeg_iff.mpr hd), if_pos hd]
          have hpart_split : ∀ r : Fin (2 * K),
              splitReg (2 * K) s (fun i => E.symm (y₀, g, d) (partEmb i)) r =
                if hr : r.val < K then splitReg K s y₀ ⟨r.val, hr⟩
                else g ⟨r.val - K, by omega⟩ := by
            intro r
            funext b
            change E.symm (y₀, g, d) (partEmb (finProdFinEquiv (r, b))) = _
            by_cases hr : r.val < K
            · rw [dif_pos hr]
              have hE1 := congrArg (fun p => splitReg K s p.1 ⟨r.val, hr⟩ b)
                (E.apply_symm_apply (y₀, g, d))
              have hE_lhs1 : (E (E.symm (y₀, g, d))).1 =
                  flatReg K s fun k j =>
                    E.symm (y₀, g, d) (partEmb (finProdFinEquiv (⟨k.val, by omega⟩, j))) := rfl
              rw [hE_lhs1, splitReg_flatReg_54] at hE1
              have hreq : (⟨r.val, by omega⟩ : Fin (2 * K)) = r := Fin.ext rfl
              rw [hreq] at hE1
              exact hE1
            · rw [dif_neg hr]
              have hE2 := congrArg (fun p => p.2.1 ⟨r.val - K, by omega⟩ b)
                (E.apply_symm_apply (y₀, g, d))
              have hE_lhs2 : (E (E.symm (y₀, g, d))).2.1 =
                  fun k j =>
                    E.symm (y₀, g, d) (partEmb (finProdFinEquiv (⟨K + k.val, by omega⟩, j))) := rfl
              rw [hE_lhs2] at hE2
              dsimp only at hE2
              have hreq : (⟨K + (r.val - K), by omega⟩ : Fin (2 * K)) = r :=
                Fin.ext (by dsimp; omega)
              rw [hreq] at hE2
              exact hE2
          let halfEquiv : Fin (2 * K) ≃ Fin K ⊕ Fin K :=
            { toFun := fun r => if hr : r.val < K then Sum.inl ⟨r.val, hr⟩ else Sum.inr ⟨r.val - K, by omega⟩
              invFun := fun
                | Sum.inl k => ⟨k.val, by omega⟩
                | Sum.inr k => ⟨K + k.val, by omega⟩
              left_inv := fun r => by
                dsimp only
                split_ifs
                · exact Fin.ext rfl
                · exact Fin.ext (by dsimp; omega)
              right_inv := fun x => by
                rcases x with k | k
                · simp [k.isLt]
                · have : ¬ K + k.val < K := by omega
                  simp [this] }
          have half_inl : ∀ k : Fin K, halfEquiv.symm (Sum.inl k) = ⟨k.val, by omega⟩ := fun _ => rfl
          have half_inr : ∀ k : Fin K, halfEquiv.symm (Sum.inr k) = ⟨K + k.val, by omega⟩ := fun _ => rfl
          dsimp only [coeff_t, k_t]
          have hprod_equiv :
              (∏ r : Fin (2 * K),
                if t (σ r) = false then dirAmp s w (splitReg (2 * K) s (fun i => E.symm (y₀, g, d) (partEmb i)) r)
                else if splitReg (2 * K) s (fun i => E.symm (y₀, g, d) (partEmb i)) r = blankSym54 s then 1 else 0) =
              ∏ x : Fin K ⊕ Fin K, match x with
                | Sum.inl k => dirAmp s w (splitReg K s y₀ k)
                | Sum.inr k => tailF k (g k) := by
            refine Fintype.prod_equiv halfEquiv _ _ fun r => ?_
            cases hr : halfEquiv r with
            | inl k =>
              have hsym : r = ⟨k.val, by omega⟩ := by
                rw [← half_inl k, ← hr, Equiv.symm_apply_apply]
              rw [hsym, hpart_split _, dif_pos k.isLt, if_pos (hσ_false k)]
            | inr k =>
              have hsym : r = ⟨K + k.val, by omega⟩ := by
                rw [← half_inr k, ← hr, Equiv.symm_apply_apply]
              have hnot : ¬ (⟨K + k.val, by omega⟩ : Fin (2 * K)).val < K := by dsimp; omega
              rw [hsym, hpart_split _, dif_neg hnot]
              have hk' : (⟨(K + k.val) - K, by omega⟩ : Fin K) = k := Fin.ext (by dsimp; omega)
              rw [hk']
          rw [hprod_equiv, Fintype.prod_sum_type]
          ring
        · rw [if_neg (fun h => hd (hdeg_iff.mp h)), if_neg hd]
      have hsumE_z := Fintype.sum_equiv E
        (fun z => ∑ z' : Qubits (n * q + e),
          if z ∘ out = y ∧ z' ∘ out = y' ∧
              ∀ j : Fin (n * q + e), (∀ i : Fin (K * s), out i ≠ j) → z j = z' j then
            φ t z * conj (φ t z')
          else 0)
        (fun p => ∑ z' : Qubits (n * q + e),
          if E.symm p ∘ out = y ∧ z' ∘ out = y' ∧
              ∀ j : Fin (n * q + e), (∀ i : Fin (K * s), out i ≠ j) → E.symm p j = z' j then
            φ t (E.symm p) * conj (φ t z')
          else 0)
        fun z => by rw [Equiv.symm_apply_apply]
      rw [hsumE_z]
      have h_inner : ∀ p : Qubits (K * s) × (Fin K → Qubits s) × ({ a : Fin (n * q + e) // a ∉ Set.range partEmb } → Bool),
          (∑ z' : Qubits (n * q + e),
            if E.symm p ∘ out = y ∧ z' ∘ out = y' ∧
                ∀ j : Fin (n * q + e), (∀ i : Fin (K * s), out i ≠ j) → E.symm p j = z' j then
              φ t (E.symm p) * conj (φ t z')
            else 0) =
          if p.1 = y then φ t (E.symm p) * conj (φ t (E.symm (y', p.2))) else 0 := by
        intro p
        have hsumE_z' := Fintype.sum_equiv E
          (fun z' => if E.symm p ∘ out = y ∧ z' ∘ out = y' ∧
                ∀ j : Fin (n * q + e), (∀ i : Fin (K * s), out i ≠ j) → E.symm p j = z' j then
              φ t (E.symm p) * conj (φ t z')
            else 0)
          (fun p' => if E.symm p ∘ out = y ∧ E.symm p' ∘ out = y' ∧
                ∀ j : Fin (n * q + e), (∀ i : Fin (K * s), out i ≠ j) → E.symm p j = E.symm p' j then
              φ t (E.symm p) * conj (φ t (E.symm p'))
            else 0)
          fun z' => by rw [Equiv.symm_apply_apply]
        rw [hsumE_z']
        rw [Finset.sum_eq_single (y', p.2)]
        · have h1 : E.symm p ∘ out = y ↔ p.1 = y := by
            rw [qubitsDecomp54_out_eq partEmb out hout]
            simp [E]
          have h2 : E.symm (y', p.2) ∘ out = y' := by
            rw [qubitsDecomp54_out_eq partEmb out hout]
            simp [E]
          have h3 : ∀ j : Fin (n * q + e), (∀ i : Fin (K * s), out i ≠ j) → E.symm p j = E.symm (y', p.2) j :=
            (qubitsDecomp54_rest_iff partEmb out hout _ _).mpr (by simp [E])
          by_cases hpy : p.1 = y
          · rw [if_pos ⟨h1.mpr hpy, h2, h3⟩, if_pos hpy]
          · rw [if_neg (fun h => hpy (h1.mp h.1)), if_neg hpy]
        · intro p' _ hp'
          rw [if_neg]
          rintro ⟨_, h2, h3⟩
          apply hp'
          have h2' : p'.1 = y' := by
            rw [qubitsDecomp54_out_eq partEmb out hout] at h2
            simpa [E] using h2
          have h3' : p.2 = p'.2 := by
            have := (qubitsDecomp54_rest_iff partEmb out hout (E.symm p) (E.symm p')).mp h3
            simpa [E] using this
          exact Prod.ext h2' h3'.symm
        · intro hnot; exact absurd (Finset.mem_univ _) hnot
      simp_rw [h_inner]
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single y]
      · have h_y :
            (∑ y_1 : (Fin K → Qubits s) × ({ a : Fin (n * q + e) // a ∉ Set.range partEmb } → Bool),
              if (y, y_1).1 = y then φ t (E.symm (y, y_1)) * conj (φ t (E.symm (y', (y, y_1).2))) else 0) =
            ∑ y_1 : (Fin K → Qubits s) × ({ a : Fin (n * q + e) // a ∉ Set.range partEmb } → Bool),
              φ t (E.symm (y, y_1)) * conj (φ t (E.symm (y', y_1))) :=
          Finset.sum_congr rfl fun y_1 _ => by dsimp only; rw [if_pos rfl]
        rw [h_y, Fintype.sum_prod_type]
        have hsum_d : ∀ g : Fin K → Qubits s,
            (∑ d : { a : Fin (n * q + e) // a ∉ Set.range partEmb } → Bool,
              φ t (E.symm (y, g, d)) * conj (φ t (E.symm (y', g, d)))) =
            (coeff_t * conj coeff_t) *
              ((∏ k : Fin K, dirAmp s w (splitReg K s y k)) *
                (∏ k : Fin K, dirAmp s w (splitReg K s y' k))) *
              ∏ k : Fin K, (tailF k (g k) * conj (tailF k (g k))) := by
          intro g
          rw [Finset.sum_eq_single (fun a => degState k_t a.1)]
          · rw [hφ_decomp y g _, hφ_decomp y' g _, if_pos rfl, if_pos rfl]
            simp only [map_mul, map_prod, conj_dirAmp]
            rw [Finset.prod_mul_distrib (f := fun k => tailF k (g k))
              (g := fun k => conj (tailF k (g k)))]
            ring
          · intro d _ hd
            rw [hφ_decomp y g d, if_neg hd, zero_mul]
          · intro hnot; exact absurd (Finset.mem_univ _) hnot
        simp_rw [hsum_d, ← Finset.mul_sum]
        have htail_sum : ∑ g : Fin K → Qubits s, ∏ k : Fin K, (tailF k (g k) * conj (tailF k (g k))) = 1 := by
          rw [← Fintype.prod_sum (fun k b => tailF k b * conj (tailF k b))]
          refine Finset.prod_eq_one fun k _ => ?_
          dsimp only [tailF]
          split_ifs
          · exact sum_normSq_dirAmp hns w hw
          · simp
        rw [htail_sum, mul_one]
        have hcoeff_sq : coeff_t * conj coeff_t =
            ((coeff1D k_t ^ 2 / (bandWeight w K * Nat.choose (2 * K) k_t) : ℝ) : ℂ) := by
          dsimp only [coeff_t]
          rw [← Complex.ofReal_mul]
          simp only [Complex.conj_ofReal, ← Complex.ofReal_mul]
          congr 1
          have hch_pos : (0 : ℝ) ≤ (Nat.choose (2 * K) k_t : ℝ)⁻¹ := by positivity
          rw [show (coeff1D k_t / Real.sqrt (bandWeight w K) * Real.sqrt ((Nat.choose (2 * K) k_t : ℝ)⁻¹)) *
                (coeff1D k_t / Real.sqrt (bandWeight w K) * Real.sqrt ((Nat.choose (2 * K) k_t : ℝ)⁻¹)) =
              (coeff1D k_t ^ 2 / (Real.sqrt (bandWeight w K)) ^ 2) *
                (Real.sqrt ((Nat.choose (2 * K) k_t : ℝ)⁻¹)) ^ 2 by ring]
          rw [Real.sq_sqrt hbw_pos.le, Real.sq_sqrt hch_pos]
          ring
        rw [hcoeff_sq, dirTensorPow, Matrix.of_apply, ← Finset.prod_mul_distrib]
      · intro y₀ _ hy₀
        simp [hy₀]
      · intro hnot; exact absurd (Finset.mem_univ y) hnot
    · rw [if_neg ht]
      have hlt : (Finset.univ.filter fun j => t j = false).card < K := lt_of_not_ge ht
      refine Finset.sum_eq_zero fun z _ => Finset.sum_eq_zero fun z' _ => ?_
      split_ifs
      · simp [hφ_lt t hlt z]
      · rfl
  simp_rw [hsum_t]
  have hsum_scalar :
      ∑ t : Qubits (2 * K),
        (if K ≤ (Finset.univ.filter fun j => t j = false).card then
          (((coeff1D (Finset.univ.filter fun j => t j = false).card) ^ 2 /
            (bandWeight w K * Nat.choose (2 * K) (Finset.univ.filter fun j => t j = false).card) : ℝ) : ℂ) *
            dirTensorPow s K w y y'
        else 0) =
      dirTensorPow s K w y y' := by
    have hfact : ∀ t : Qubits (2 * K),
        (if K ≤ (Finset.univ.filter fun j => t j = false).card then
          (((coeff1D (Finset.univ.filter fun j => t j = false).card) ^ 2 /
            (bandWeight w K * Nat.choose (2 * K) (Finset.univ.filter fun j => t j = false).card) : ℝ) : ℂ) *
            dirTensorPow s K w y y'
        else 0) =
        (if K ≤ (Finset.univ.filter fun j => t j = false).card then
          (((coeff1D (Finset.univ.filter fun j => t j = false).card) ^ 2 /
            (bandWeight w K * Nat.choose (2 * K) (Finset.univ.filter fun j => t j = false).card) : ℝ) : ℂ)
        else 0) * dirTensorPow s K w y y' := fun t => by
      split_ifs <;> simp
    simp_rw [hfact]
    rw [← Finset.sum_mul]
    suffices h : ∑ t : Qubits (2 * K),
        (if K ≤ (Finset.univ.filter fun j => t j = false).card then
          (((coeff1D (Finset.univ.filter fun j => t j = false).card) ^ 2 /
            (bandWeight w K * Nat.choose (2 * K) (Finset.univ.filter fun j => t j = false).card) : ℝ) : ℂ)
        else 0) = 1 by
      rw [h, one_mul]
    have hfib := Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (Qubits (2 * K))))
      (t := Finset.Icc 0 (2 * K))
      (g := fun t : Qubits (2 * K) => (Finset.univ.filter fun j => t j = false).card)
      (f := fun t : Qubits (2 * K) =>
        if K ≤ (Finset.univ.filter fun j => t j = false).card then
          (((coeff1D (Finset.univ.filter fun j => t j = false).card) ^ 2 /
            (bandWeight w K * Nat.choose (2 * K) (Finset.univ.filter fun j => t j = false).card) : ℝ) : ℂ)
        else 0)
      (fun t _ => Finset.mem_Icc.mpr ⟨Nat.zero_le _, by
        simpa using Finset.card_filter_le (Finset.univ : Finset (Fin (2 * K))) fun j => t j = false⟩)
    rw [← hfib]
    have hfib_val : ∀ k ∈ Finset.Icc 0 (2 * K),
        (∑ t ∈ Finset.univ.filter (fun t : Qubits (2 * K) => (Finset.univ.filter fun j => t j = false).card = k),
          if K ≤ (Finset.univ.filter fun j => t j = false).card then
            (((coeff1D (Finset.univ.filter fun j => t j = false).card) ^ 2 /
              (bandWeight w K * Nat.choose (2 * K) (Finset.univ.filter fun j => t j = false).card) : ℝ) : ℂ)
          else 0) =
        if K ≤ k then (((coeff1D k) ^ 2 / bandWeight w K : ℝ) : ℂ) else 0 := by
      intro k hk
      have hk_le : k ≤ 2 * K := (Finset.mem_Icc.mp hk).2
      have hcongr : ∑ t ∈ Finset.univ.filter (fun t : Qubits (2 * K) => (Finset.univ.filter fun j => t j = false).card = k),
            (if K ≤ (Finset.univ.filter fun j => t j = false).card then
              (((coeff1D (Finset.univ.filter fun j => t j = false).card) ^ 2 /
                (bandWeight w K * Nat.choose (2 * K) (Finset.univ.filter fun j => t j = false).card) : ℝ) : ℂ)
            else 0) =
          ∑ _t ∈ Finset.univ.filter (fun t : Qubits (2 * K) => (Finset.univ.filter fun j => t j = false).card = k),
            if K ≤ k then
              (((coeff1D k) ^ 2 / (bandWeight w K * Nat.choose (2 * K) k) : ℝ) : ℂ)
            else 0 := by
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [(Finset.mem_filter.mp ht).2]
      rw [hcongr, Finset.sum_const, card_qubits_filter_false_eq_choose]
      split_ifs with hKk
      · have hch_ne : (Nat.choose (2 * K) k : ℝ) ≠ 0 :=
          (Nat.cast_pos.mpr (Nat.choose_pos hk_le)).ne'
        rw [nsmul_eq_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_mul]
        congr 1
        field_simp [hch_ne]
      · simp
    rw [Finset.sum_congr rfl hfib_val]
    have hIcc : (∑ k ∈ Finset.Icc 0 (2 * K),
        if K ≤ k then (((coeff1D k) ^ 2 / bandWeight w K : ℝ) : ℂ) else 0) =
        ∑ k ∈ Finset.Icc K (2 * K), (((coeff1D k) ^ 2 / bandWeight w K : ℝ) : ℂ) := by
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [hIcc, ← Complex.ofReal_sum, ← Finset.sum_div, ← hbw_eq, div_self hbw_pos.ne', Complex.ofReal_one]
  exact hsum_scalar

end Aux_channel_54

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

theorem solution :
    ∀ (n K D q e : ℕ), 1 ≤ n → 1 ≤ K → 2 * K + 1 ≤ D → D ≤ 2 ^ q →
      let s := Nat.clog 2 n + 1
      ∀ (partEmb : Fin (2 * K * s) ↪ Fin (n * q + e))
        (meas : Fin (2 * K) ↪ Fin (n * q + e))
        (out : Fin (K * s) ↪ Fin (n * q + e))
        (V : Matrix (Qubits (n * q + e)) (Qubits (n * q + e)) ℂ)
        (W : Qubits (2 * K) → Matrix (Qubits (n * q + e)) (Qubits (n * q + e)) ℂ)
        (degState : ℕ → Qubits (n * q + e)),
        (∀ j : Fin (2 * K), meas j = partEmb (finProdFinEquiv (j, ⟨0, Nat.succ_pos _⟩))) →
        (∀ (k : Fin K) (j : Fin s),
          out (finProdFinEquiv (k, j)) = partEmb (finProdFinEquiv (⟨k.val, by omega⟩, j))) →
        (∀ (α : Fin n → ℕ) (hk : K ≤ ∑ i, α i ∧ ∑ i, α i ≤ 2 * K),
          act V (padKet e (ket (flatReg n q fun i => natToBits q (α i)))) =
            embedPartAndDeg54 partEmb (multinomKet54 n s K α hk) (degState (∑ i, α i))) →
        (∀ t : Qubits (2 * K), K ≤ (Finset.univ.filter fun j => t j = false).card →
          ∃ σ : Equiv.Perm (Fin (2 * K)),
            (∀ k : Fin K, t (σ ⟨k.val, by omega⟩) = false) ∧
            ∀ x : Qubits (n * q + e),
              act (W t) (ket x) = ket (permPartReg54 partEmb σ x)) →
        ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
          measChannelOut V W meas out (padKet e (bandKet n q K w)) = dirTensorPow s K w :=
  fun n K D q e hn hK hKD hDq =>
    Aux_channel_54.band_channel_algebra_54_aux
      Aux_hermite_54.coeff1D
      (fun hn => Aux_hermite_54.hermCoeff_formula hn)
      Aux_hermite_54.p1D53_eq_sum_coeff1D_sq
      n K D q e hn hK hKD hDq
