-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.hermite_band_bounds_53
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-24T07:31:22.867042+00:00
-- url     : https://prove2.me/submissions/cf3262fe-37c1-45d4-9cef-79851619cd7a

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53

set_option autoImplicit false

namespace Aux_w_53_hermite

open MeasureTheory Filter Polynomial QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open scoped Real Topology Nat ENNReal

/-! ### Part 1: 1D Gaussian Density, Orthonormal Hermite Functions, and `sgn` Coefficients -/

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

noncomputable def coeff1D (k : ℕ) : ℝ :=
  ∫ x : ℝ, (sgn x : ℝ) * h1D k x ∂(ProbabilityTheory.gaussianReal 0 1)

lemma coeff1D_odd (s : ℕ) :
    coeff1D (2 * s + 1) =
      Real.sqrt (2 / Real.pi) * (Real.sqrt (2 * s + 1 : ℝ) * h1D (2 * s) 0) / (2 * s + 1 : ℝ) := by
  let j := 0
  let k := 2 * s + 1
  have hM : coeff1D k = 2 * ∫ x in Set.Ioi (0 : ℝ), h1D j x * h1D k x * phi x := by
    rw [coeff1D, ProbabilityTheory.integral_gaussianReal_eq_integral_smul one_ne_zero]
    have heq : (fun x : ℝ => ProbabilityTheory.gaussianPDFReal 0 1 x • ((sgn x : ℝ) * h1D k x)) =
        fun x => (sgn x : ℝ) * h1D j x * h1D k x * phi x := by
      ext x; simp [j, h1D_zero_fn, phi, smul_eq_mul]; ring
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
        have habs_sgn : |(sgn x : ℝ)| = 1 := by simp only [sgn]; split_ifs <;> norm_num
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
          have hjpow : (-1 : ℝ) ^ j = 1 := by simp [j]
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
    let Pj : Polynomial ℝ := 1
    let Pk : Polynomial ℝ :=
      Polynomial.C (Real.sqrt (k.factorial : ℝ))⁻¹ * (Polynomial.hermite k).map (algebraMap ℤ ℝ)
    let Pjd : Polynomial ℝ := 0
    let Pkd : Polynomial ℝ :=
      Polynomial.C (Real.sqrt (k : ℝ) * (Real.sqrt ((k - 1).factorial : ℝ))⁻¹) *
        (Polynomial.hermite (k - 1)).map (algebraMap ℤ ℝ)
    refine ⟨Pjd * Pk - Pj * Pkd, ?_⟩
    ext x
    have hPj : Pj.eval x = h1D j x := by simp [Pj, j, h1D_zero_fn]
    have hPk : Pk.eval x = h1D k x := by simp [Pk, h1D, Hpoly, Polynomial.aeval_def, Polynomial.eval_map]
    have hPjd : Pjd.eval x = h1D_deriv j x := by simp [Pjd, j, h1D_deriv]
    have hPkd : Pkd.eval x = h1D_deriv k x := by
      simp [Pkd, k, h1D_deriv, h1D, Hpoly, Polynomial.aeval_def, Polynomial.eval_map, mul_assoc]
    simp only [F, Polynomial.eval_sub, Polynomial.eval_mul, hPj, hPk, hPjd, hPkd]
    ring
  obtain ⟨Q, hQ⟩ := hF_poly
  have hF_tendsto : Tendsto F atTop (𝓝 0) := hQ ▸ tendsto_poly_mul_phi_atTop Q
  have hF'_int : IntegrableOn (fun x => ((k : ℝ) - j) * (h1D j x * h1D k x * phi x)) (Set.Ioi 0) volume :=
    ((integrable_h1D_mul_h1D_mul_phi j k).const_mul ((k : ℝ) - j)).integrableOn
  have hint_eq := integral_Ioi_of_hasDerivAt_of_tendsto hF_cont.continuousWithinAt hF_deriv hF'_int hF_tendsto
  rw [integral_const_mul, zero_sub] at hint_eq
  have hF0 : F 0 = -phi 0 * Real.sqrt (2 * s + 1 : ℝ) * h1D (2 * s) 0 := by
    have hj_zero : h1D j 0 = 1 := h1D_zero_fn 0
    have hkd : h1D_deriv k 0 = Real.sqrt (2 * s + 1 : ℝ) * h1D (2 * s) 0 := by
      simp [k, h1D_deriv]
    have hjd : h1D_deriv j 0 = 0 := by simp [j, h1D_deriv]
    dsimp only [F]
    rw [hjd, hj_zero, hkd]
    ring
  rw [hF0] at hint_eq
  have hne : (2 * s + 1 : ℝ) ≠ 0 := by positivity
  have hint_Ioi : ∫ x in Set.Ioi (0 : ℝ), h1D j x * h1D k x * phi x =
      (phi 0 * Real.sqrt (2 * s + 1 : ℝ) * h1D (2 * s) 0) / (2 * s + 1 : ℝ) := by
    have hk' : ((k : ℝ) - (j : ℝ)) = 2 * s + 1 := by simp [j, k]
    have h1 : (2 * s + 1 : ℝ) * ∫ x in Set.Ioi (0 : ℝ), h1D j x * h1D k x * phi x =
        phi 0 * Real.sqrt (2 * s + 1 : ℝ) * h1D (2 * s) 0 := by
      calc (2 * s + 1 : ℝ) * ∫ x in Set.Ioi (0 : ℝ), h1D j x * h1D k x * phi x
          = ((k : ℝ) - (j : ℝ)) * ∫ x in Set.Ioi (0 : ℝ), h1D j x * h1D k x * phi x := by rw [hk']
        _ = -(-phi 0 * Real.sqrt (2 * s + 1 : ℝ) * h1D (2 * s) 0) := hint_eq
        _ = phi 0 * Real.sqrt (2 * s + 1 : ℝ) * h1D (2 * s) 0 := by ring
    rw [eq_div_iff hne, mul_comm]
    exact h1
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
  calc 2 * ((phi 0 * Real.sqrt (2 * s + 1 : ℝ) * h1D (2 * s) 0) / (2 * s + 1 : ℝ))
      = ((2 * phi 0) * (Real.sqrt (2 * s + 1 : ℝ) * h1D (2 * s) 0)) / (2 * s + 1 : ℝ) := by ring
    _ = _ := by rw [h2phi]

lemma h1D_even_zero_sq_lower (r : ℕ) :
    1 ≤ (4 * r + 1 : ℝ) * ((h1D (2 * r) 0) ^ 2) ^ 2 := by
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
  let a : ℕ → ℝ := fun k => ((2 * k - 1)‼ : ℝ) / ((2 ^ k * k.factorial : ℕ) : ℝ)
  have hsq_eq : (h1D (2 * r) 0) ^ 2 = a r := by
    rw [h1D, hcoeff, mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _), hfac_eq r]
    have hneg1 : ((-1 : ℝ) ^ r) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have hdf_pos : (0 : ℝ) < (2 * r - 1)‼ := Nat.cast_pos.mpr (Nat.doubleFactorial_pos _)
    have hden_pos : (0 : ℝ) < (2 ^ r * r.factorial : ℕ) :=
      Nat.cast_pos.mpr (mul_pos (pow_pos (by norm_num) _) (Nat.factorial_pos _))
    rw [mul_pow, hneg1, one_mul, Nat.cast_mul]
    dsimp [a]
    field_simp
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
  have hbound : ∀ k : ℕ, 1 ≤ (4 * k + 1 : ℝ) * (a k) ^ 2 := by
    intro k
    induction k with
    | zero => simp [a]
    | succ k ih =>
      rw [ha_step]
      have hden : (0 : ℝ) < (4 * k + 1 : ℝ) * (2 * k + 2 : ℝ) ^ 2 := by positivity
      have hnum : (4 * (k : ℝ) + 1) * (2 * k + 2) ^ 2 ≤ (4 * ((k + 1 : ℕ) : ℝ) + 1) * (2 * k + 1) ^ 2 := by
        push_cast; nlinarith
      have hratio : 1 ≤ ((4 * ((k + 1 : ℕ) : ℝ) + 1) * (2 * k + 1 : ℝ) ^ 2) /
          ((4 * k + 1 : ℝ) * (2 * k + 2 : ℝ) ^ 2) := (one_le_div hden).mpr hnum
      have halg : (4 * ((k + 1 : ℕ) : ℝ) + 1) * (a k * (2 * k + 1 : ℝ) / (2 * k + 2 : ℝ)) ^ 2 =
          (((4 * ((k + 1 : ℕ) : ℝ) + 1) * (2 * k + 1 : ℝ) ^ 2) /
            ((4 * k + 1 : ℝ) * (2 * k + 2 : ℝ) ^ 2)) * ((4 * k + 1 : ℝ) * (a k) ^ 2) := by
        have h1 : (4 * (k : ℝ) + 1) ≠ 0 := by positivity
        have h2 : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
        field_simp
      rw [halg]
      calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
        _ ≤ _ := mul_le_mul hratio ih (by positivity) (by positivity)
  rw [hsq_eq]
  exact hbound r

lemma coeff1D_odd_sq_ge (s : ℕ) :
    2 / (Real.pi * Real.sqrt (4 * s + 1 : ℝ) * (2 * s + 1 : ℝ)) ≤ (coeff1D (2 * s + 1)) ^ 2 := by
  rw [coeff1D_odd s, div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)]
  have hs_pos : (0 : ℝ) < 2 * s + 1 := by positivity
  have h4s_pos : (0 : ℝ) < 4 * s + 1 := by positivity
  have hlow := h1D_even_zero_sq_lower s
  have ha_ge : 1 / Real.sqrt (4 * s + 1 : ℝ) ≤ (h1D (2 * s) 0) ^ 2 := by
    rw [div_le_iff₀ (Real.sqrt_pos.mpr h4s_pos)]
    have hsq : (1 : ℝ) ^ 2 ≤ (h1D (2 * s) 0 ^ 2 * Real.sqrt (4 * s + 1 : ℝ)) ^ 2 := by
      calc (1 : ℝ) ^ 2 = 1 := one_pow 2
        _ ≤ (4 * s + 1 : ℝ) * ((h1D (2 * s) 0) ^ 2) ^ 2 := hlow
        _ = (h1D (2 * s) 0 ^ 2 * Real.sqrt (4 * s + 1 : ℝ)) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt h4s_pos.le]; ring
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hsq
  calc 2 / (Real.pi * Real.sqrt (4 * s + 1 : ℝ) * (2 * s + 1 : ℝ))
      = (2 / Real.pi) * ((2 * s + 1 : ℝ) * (1 / Real.sqrt (4 * s + 1 : ℝ))) / (2 * s + 1 : ℝ) ^ 2 := by
          field_simp
    _ ≤ (2 / Real.pi) * ((2 * s + 1 : ℝ) * (h1D (2 * s) 0) ^ 2) / (2 * s + 1 : ℝ) ^ 2 := by
          gcongr

lemma sum_coeff1D_sq_le_one (S : Finset ℕ) :
    ∑ k ∈ S, (coeff1D k) ^ 2 ≤ 1 := by
  let γ1 := ProbabilityTheory.gaussianReal 0 1
  have hsgn_meas : Measurable (fun x : ℝ => (sgn x : ℝ)) :=
    measurable_from_top.comp (Measurable.ite measurableSet_Ici measurable_const measurable_const)
  have hsgn_sq_int : Integrable (fun x : ℝ => ((sgn x : ℝ) ^ 2)) γ1 := by
    have : (fun x : ℝ => ((sgn x : ℝ) ^ 2)) = fun _ => 1 := by
      ext x; simp only [sgn]; split_ifs <;> norm_num
    rw [this]; exact integrable_const 1
  have hsg_int : Integrable (fun x : ℝ => (sgn x : ℝ) * ∑ k ∈ S, coeff1D k * h1D k x) γ1 := by
    have heq : (fun x : ℝ => (sgn x : ℝ) * ∑ k ∈ S, coeff1D k * h1D k x) =
        fun x => ∑ k ∈ S, coeff1D k * ((sgn x : ℝ) * h1D k x * h1D 0 x) := by
      ext x
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [h1D_zero_fn]; ring
    rw [heq]
    exact integrable_finsetSum _ fun k _ => (integrable_sgn_mul_h1D_mul_h1D k 0).const_mul _
  have hgg_int : Integrable (fun x : ℝ => (∑ k ∈ S, coeff1D k * h1D k x) ^ 2) γ1 := by
    have heq : (fun x : ℝ => (∑ k ∈ S, coeff1D k * h1D k x) ^ 2) =
        fun x => ∑ k ∈ S, ∑ l ∈ S, (coeff1D k * coeff1D l) * (h1D k x * h1D l x) := by
      ext x
      rw [sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [heq]
    exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
      (integrable_h1D_mul_h1D k l).const_mul _
  have h1 : ∫ x, (sgn x : ℝ) ^ 2 ∂γ1 = 1 := by
    have heq : (fun x : ℝ => (sgn x : ℝ) ^ 2) = fun _ => 1 := by
      ext x; simp only [sgn]; split_ifs <;> norm_num
    rw [heq, integral_const]; simp
  have h2 : ∫ x, (sgn x : ℝ) * ∑ k ∈ S, coeff1D k * h1D k x ∂γ1 = ∑ k ∈ S, (coeff1D k) ^ 2 := by
    have heq : (fun x : ℝ => (sgn x : ℝ) * ∑ k ∈ S, coeff1D k * h1D k x) =
        fun x => ∑ k ∈ S, coeff1D k * ((sgn x : ℝ) * h1D k x) := by
      ext x; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
    rw [heq, integral_finsetSum _ fun k _ => by
      have : (fun x => coeff1D k * ((sgn x : ℝ) * h1D k x)) =
          fun x => coeff1D k * ((sgn x : ℝ) * h1D k x * h1D 0 x) := by
        ext x; simp [h1D_zero_fn]
      rw [this]; exact (integrable_sgn_mul_h1D_mul_h1D k 0).const_mul _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]
    dsimp only [γ1, coeff1D]
    rw [sq]
  have h3 : ∫ x, (∑ k ∈ S, coeff1D k * h1D k x) ^ 2 ∂γ1 = ∑ k ∈ S, (coeff1D k) ^ 2 := by
    have heq : (fun x : ℝ => (∑ k ∈ S, coeff1D k * h1D k x) ^ 2) =
        fun x => ∑ k ∈ S, ∑ l ∈ S, (coeff1D k * coeff1D l) * (h1D k x * h1D l x) := by
      ext x
      rw [sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [heq, integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
      (integrable_h1D_mul_h1D k l).const_mul _]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [integral_finsetSum _ fun l _ => (integrable_h1D_mul_h1D k l).const_mul _]
    simp_rw [integral_const_mul, h1D_orthonormal]
    simp [hk, sq]
  have hnn : 0 ≤ ∫ x, ((sgn x : ℝ) - ∑ k ∈ S, coeff1D k * h1D k x) ^ 2 ∂γ1 :=
    integral_nonneg fun x => sq_nonneg _
  have hexp : ∫ x, ((sgn x : ℝ) - ∑ k ∈ S, coeff1D k * h1D k x) ^ 2 ∂γ1 =
      (∫ x, (sgn x : ℝ) ^ 2 ∂γ1 - 2 * ∫ x, (sgn x : ℝ) * ∑ k ∈ S, coeff1D k * h1D k x ∂γ1) +
        ∫ x, (∑ k ∈ S, coeff1D k * h1D k x) ^ 2 ∂γ1 := by
    calc ∫ x, ((sgn x : ℝ) - ∑ k ∈ S, coeff1D k * h1D k x) ^ 2 ∂γ1
        = ∫ x, (((sgn x : ℝ) ^ 2 - 2 * ((sgn x : ℝ) * ∑ k ∈ S, coeff1D k * h1D k x)) +
            (∑ k ∈ S, coeff1D k * h1D k x) ^ 2) ∂γ1 :=
          integral_congr_ae (ae_of_all _ fun x => by ring)
      _ = (∫ x, (sgn x : ℝ) ^ 2 - 2 * ((sgn x : ℝ) * ∑ k ∈ S, coeff1D k * h1D k x) ∂γ1) +
            ∫ x, (∑ k ∈ S, coeff1D k * h1D k x) ^ 2 ∂γ1 :=
          integral_add (hsgn_sq_int.sub (hsg_int.const_mul 2)) hgg_int
      _ = _ := by rw [integral_sub hsgn_sq_int (hsg_int.const_mul 2), integral_const_mul]
  rw [hexp, h1, h2, h3] at hnn
  linarith

/-! ### Part 2: Multivariate Hermite Orthonormality & Orthogonal-Projection Invariance -/

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

/-! ### Part 3: Rotational Invariance of `bandWeight` & 1D Bounds -/

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

lemma bandWeight_eq_I_deg_diff {n : ℕ} (w : E n) (K : ℕ) :
    bandWeight w K =
      (∑ α ∈ I_deg n (2 * K), (coeff_nd (fun x => (ltf w 0 x : ℝ)) α) ^ 2) -
        if K = 0 then 0 else ∑ α ∈ I_deg n (K - 1), (coeff_nd (fun x => (ltf w 0 x : ℝ)) α) ^ 2 := by
  unfold bandWeight
  simp_rw [hermCoeff_eq_coeff_nd]
  let f := fun x : E n => (ltf w 0 x : ℝ)
  let emb : (Fin n → Fin (2 * K + 1)) ↪ (Fin n → ℕ) :=
    ⟨fun α i => (α i : ℕ), fun α β h => by ext i; exact congrFun h i⟩
  have hsum_emb :
      (∑ α : Fin n → Fin (2 * K + 1),
        if K ≤ ∑ i, (α i : ℕ) ∧ ∑ i, (α i : ℕ) ≤ 2 * K then (coeff_nd f (emb α)) ^ 2 else 0) =
      ∑ γ ∈ (I_deg n (2 * K)).filter (fun α => K ≤ totalDeg α), (coeff_nd f γ) ^ 2 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun α _ => emb α) ?_ ?_ ?_ ?_
    · intro α hα
      rcases Finset.mem_filter.mp hα with ⟨_, hα⟩
      refine Finset.mem_filter.mpr ⟨mem_I_deg.mpr hα.2, hα.1⟩
    · intro α _ β _ h; exact emb.injective h
    · intro γ hγ
      rcases Finset.mem_filter.mp hγ with ⟨hγ1, hγ2⟩
      rw [mem_I_deg] at hγ1
      unfold totalDeg at hγ1 hγ2
      have hcoord : ∀ i : Fin n, γ i < 2 * K + 1 := fun i => by
        have hle := Finset.single_le_sum (fun j _ => Nat.zero_le (γ j)) (Finset.mem_univ i)
        omega
      refine ⟨fun i => ⟨γ i, hcoord i⟩, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hγ2, hγ1⟩⟩
      · ext i; rfl
    · intro α _; rfl
  change (∑ α : Fin n → Fin (2 * K + 1),
      if K ≤ ∑ i, (α i : ℕ) ∧ ∑ i, (α i : ℕ) ≤ 2 * K then (coeff_nd f (emb α)) ^ 2 else 0) = _
  rw [hsum_emb]
  cases K with
  | zero =>
    simp only [mul_zero, zero_le, Finset.filter_true, ↓reduceIte, sub_zero]
    rfl
  | succ K' =>
    have hsplit : I_deg n (2 * (K' + 1)) =
        (I_deg n (2 * (K' + 1))).filter (fun α => K' + 1 ≤ totalDeg α) ∪ I_deg n K' := by
      ext α
      simp only [Finset.mem_union, Finset.mem_filter, mem_I_deg]
      omega
    have hdisj : Disjoint ((I_deg n (2 * (K' + 1))).filter (fun α => K' + 1 ≤ totalDeg α))
        (I_deg n K') := by
      rw [Finset.disjoint_left]
      intro α h1 h2
      simp only [Finset.mem_filter, mem_I_deg] at h1 h2
      omega
    have hadd := Finset.sum_union hdisj (f := fun α => (coeff_nd f α) ^ 2)
    rw [← hsplit] at hadd
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    linarith

lemma bandWeight_comp_isom {n : ℕ} (w : E n) (R : E n ≃ₗᵢ[ℝ] E n) (K : ℕ) :
    bandWeight (R.symm w) K = bandWeight w K := by
  have heq : (fun x : E n => (ltf (R.symm w) 0 x : ℝ)) = (fun x => (ltf w 0 x : ℝ)) ∘ R := by
    ext x
    simp only [Function.comp_def, ltf, sub_zero]
    rw [← R.inner_map_map (R.symm w) x, R.apply_symm_apply]
  rw [bandWeight_eq_I_deg_diff (R.symm w) K, bandWeight_eq_I_deg_diff w K]
  simp_rw [heq]
  rw [sum_I_deg_coeff_sq_comp_isom R (memLp_ltf w) (2 * K)]
  split_ifs
  · rfl
  · rw [sum_I_deg_coeff_sq_comp_isom R (memLp_ltf w) (K - 1)]

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

lemma bandWeight_single_zero {n : ℕ} (hn : 1 ≤ n) (K : ℕ) :
    bandWeight (EuclideanSpace.single (⟨0, hn⟩ : Fin n) 1) K =
      ∑ k ∈ Finset.Icc K (2 * K), (coeff1D k) ^ 2 := by
  let i₀ : Fin n := ⟨0, hn⟩
  unfold bandWeight
  simp_rw [hermCoeff_eq_coeff_nd, coeff_nd_single_zero hn]
  have hsum :
      (∑ α : Fin n → Fin (2 * K + 1),
        if K ≤ ∑ i, (α i : ℕ) ∧ ∑ i, (α i : ℕ) ≤ 2 * K then
          (if ∀ i : Fin n, i ≠ i₀ → (α i : ℕ) = 0 then coeff1D (α i₀) else 0) ^ 2
        else 0) =
      ∑ k ∈ Finset.Icc K (2 * K), (coeff1D k) ^ 2 := by
    let P0 : (Fin n → Fin (2 * K + 1)) → Prop := fun α => ∀ i : Fin n, i ≠ i₀ → (α i : ℕ) = 0
    have hsplit : (Finset.univ : Finset (Fin n → Fin (2 * K + 1))) =
        Finset.univ.filter P0 ∪ Finset.univ.filter (fun α => ¬ P0 α) := by
      ext α
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    have hdisj : Disjoint (Finset.univ.filter P0) (Finset.univ.filter (fun α => ¬ P0 α)) := by
      rw [Finset.disjoint_left]; intro α h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    rw [hsplit, Finset.sum_union hdisj]
    have hzero : ∑ α ∈ Finset.univ.filter (fun α => ¬ P0 α),
        (if K ≤ ∑ i, (α i : ℕ) ∧ ∑ i, (α i : ℕ) ≤ 2 * K then
          (if P0 α then coeff1D (α i₀) else 0) ^ 2
        else 0) = 0 := by
      refine Finset.sum_eq_zero fun α hα => ?_
      rw [if_neg (Finset.mem_filter.mp hα).2]; split_ifs <;> simp
    rw [hzero, add_zero, ← Finset.sum_filter]
    refine Finset.sum_bij (fun α _ => (α i₀ : ℕ)) ?_ ?_ ?_ ?_
    · intro α hα
      rcases Finset.mem_filter.mp hα with ⟨h1, h2⟩
      have hP0 : P0 α := (Finset.mem_filter.mp h1).2
      have hdeg : ∑ i : Fin n, (α i : ℕ) = (α i₀ : ℕ) := by
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i₀)]
        have hs0 : ∑ i ∈ Finset.univ.erase i₀, (α i : ℕ) = 0 :=
          Finset.sum_eq_zero fun i hi => hP0 i (Finset.ne_of_mem_erase hi)
        rw [hs0, add_zero]
      rw [Finset.mem_Icc, ← hdeg]
      exact h2
    · intro α hα β hβ heq
      have hPα : P0 α := (Finset.mem_filter.mp (Finset.mem_filter.mp hα).1).2
      have hPβ : P0 β := (Finset.mem_filter.mp (Finset.mem_filter.mp hβ).1).2
      ext i
      by_cases hi : i = i₀
      · subst hi; exact heq
      · rw [hPα i hi, hPβ i hi]
    · intro k hk
      rw [Finset.mem_Icc] at hk
      have hlt : k < 2 * K + 1 := by omega
      let αk : Fin n → Fin (2 * K + 1) := fun i =>
        if i = i₀ then ⟨k, hlt⟩ else ⟨0, Nat.zero_lt_succ _⟩
      refine ⟨αk, ?_, by simp [αk]⟩
      have h0 : P0 αk := fun i hi => by simp [αk, hi]
      have hdeg : ∑ i : Fin n, (αk i : ℕ) = k := by
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i₀)]
        have hs0 : ∑ i ∈ Finset.univ.erase i₀, (αk i : ℕ) = 0 :=
          Finset.sum_eq_zero fun i hi => h0 i (Finset.ne_of_mem_erase hi)
        rw [hs0, add_zero]
        simp [αk]
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩,
        by rw [hdeg]; exact hk⟩
    · intro α hα
      rcases Finset.mem_filter.mp hα with ⟨h1, _⟩
      have hP0 : P0 α := (Finset.mem_filter.mp h1).2
      rw [if_pos hP0]
  exact hsum

lemma bandWeight_eq_bandWeight_one {n K : ℕ} (w : E n) (hw : ‖w‖ = 1) :
    bandWeight w K = bandWeight (EuclideanSpace.single (0 : Fin 1) 1) K := by
  have hn : 1 ≤ n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    have hw0 : w = 0 := Subsingleton.elim _ _
    rw [hw0, norm_zero] at hw
    norm_num at hw
  let i₀ : Fin n := ⟨0, hn⟩
  let e₀ : E n := EuclideanSpace.single i₀ 1
  have he₀ : ‖e₀‖ = 1 := by simp [e₀]
  obtain ⟨R, hR⟩ := exists_isom_unit_to_unit e₀ w he₀ hw
  have hsymm : R.symm w = e₀ := by
    rw [← hR, R.symm_apply_apply]
  calc bandWeight w K = bandWeight (R.symm w) K := (bandWeight_comp_isom w R K).symm
    _ = bandWeight e₀ K := by rw [hsymm]
    _ = ∑ k ∈ Finset.Icc K (2 * K), (coeff1D k) ^ 2 := bandWeight_single_zero hn K
    _ = bandWeight (EuclideanSpace.single (0 : Fin 1) 1) K := (bandWeight_single_zero (n := 1) le_rfl K).symm

lemma bandWeight_one_bounds (K : ℕ) (hK : 1 ≤ K) :
    (1 / (4 * Real.pi)) / Real.sqrt K ≤ bandWeight (EuclideanSpace.single (0 : Fin 1) 1) K ∧
      bandWeight (EuclideanSpace.single (0 : Fin 1) 1) K ≤ 1 := by
  have h0 : (⟨0, Nat.le_refl 1⟩ : Fin 1) = 0 := rfl
  rw [← h0, bandWeight_single_zero (n := 1) (Nat.le_refl 1) K]
  refine ⟨?_, sum_coeff1D_sq_le_one _⟩
  let S : Finset ℕ := Finset.Ico (K / 2) K
  have himg_sub : S.image (fun s => 2 * s + 1) ⊆ Finset.Icc K (2 * K) := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨s, hs, rfl⟩
    rw [Finset.mem_Ico] at hs
    rw [Finset.mem_Icc]
    omega
  have hsum_ge : ∑ s ∈ S, (coeff1D (2 * s + 1)) ^ 2 ≤ ∑ k ∈ Finset.Icc K (2 * K), (coeff1D k) ^ 2 := by
    have hinj : Function.Injective (fun s => 2 * s + 1) := fun a b h => by
      dsimp only at h; omega
    rw [← Finset.sum_image (f := fun k => (coeff1D k) ^ 2) (fun a _ b _ h => hinj h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg himg_sub fun _ _ _ => sq_nonneg _
  have hterm : ∀ s ∈ S,
      1 / (2 * Real.pi * (K : ℝ) * Real.sqrt K) ≤ (coeff1D (2 * s + 1)) ^ 2 := by
    intro s hs
    rw [Finset.mem_Ico] at hs
    have h4s_le : (4 * s + 1 : ℝ) ≤ 4 * (K : ℝ) := by
      have : 4 * s + 1 ≤ 4 * K := by omega
      exact_mod_cast this
    have h2s_le : (2 * s + 1 : ℝ) ≤ 2 * (K : ℝ) := by
      have : 2 * s + 1 ≤ 2 * K := by omega
      exact_mod_cast this
    have hsqrt_le : Real.sqrt (4 * s + 1 : ℝ) ≤ 2 * Real.sqrt K := by
      calc Real.sqrt (4 * s + 1 : ℝ) ≤ Real.sqrt (4 * (K : ℝ)) := Real.sqrt_le_sqrt h4s_le
        _ = Real.sqrt 4 * Real.sqrt K := Real.sqrt_mul (by norm_num) _
        _ = 2 * Real.sqrt K := by norm_num
    have hK_pos : (0 : ℝ) < K := by exact_mod_cast hK
    have hden_le : Real.pi * Real.sqrt (4 * s + 1 : ℝ) * (2 * s + 1 : ℝ) ≤
        Real.pi * (2 * Real.sqrt K) * (2 * (K : ℝ)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrt_le Real.pi_pos.le) h2s_le
        (by positivity) (by positivity)
    have hlow : 2 / (Real.pi * (2 * Real.sqrt K) * (2 * (K : ℝ))) ≤
        2 / (Real.pi * Real.sqrt (4 * s + 1 : ℝ) * (2 * s + 1 : ℝ)) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hden_le
    have hEq : 1 / (2 * Real.pi * (K : ℝ) * Real.sqrt K) =
        2 / (Real.pi * (2 * Real.sqrt K) * (2 * (K : ℝ))) := by
      have h1 : (K : ℝ) ≠ 0 := hK_pos.ne'
      have h2 : Real.sqrt K ≠ 0 := (Real.sqrt_pos.mpr hK_pos).ne'
      have h3 : Real.pi ≠ 0 := Real.pi_pos.ne'
      field_simp
    exact hEq ▸ hlow.trans (coeff1D_odd_sq_ge s)
  have hK_pos : (0 : ℝ) < K := by exact_mod_cast hK
  have hcard : (K : ℝ) / 2 ≤ (S.card : ℝ) := by
    have hnat : K ≤ 2 * S.card := by
      dsimp [S]
      rw [Nat.card_Ico]
      omega
    have hreal : (K : ℝ) ≤ 2 * (S.card : ℝ) := by exact_mod_cast hnat
    linarith
  have hsum_card : (S.card : ℝ) * (1 / (2 * Real.pi * (K : ℝ) * Real.sqrt K)) ≤
      ∑ s ∈ S, (coeff1D (2 * s + 1)) ^ 2 := by
    calc (S.card : ℝ) * (1 / (2 * Real.pi * (K : ℝ) * Real.sqrt K))
        = ∑ _ ∈ S, (1 / (2 * Real.pi * (K : ℝ) * Real.sqrt K)) := by simp [nsmul_eq_mul]
      _ ≤ ∑ s ∈ S, (coeff1D (2 * s + 1)) ^ 2 := Finset.sum_le_sum hterm
  have hfinal : (1 / (4 * Real.pi)) / Real.sqrt K ≤
      (S.card : ℝ) * (1 / (2 * Real.pi * (K : ℝ) * Real.sqrt K)) := by
    calc (1 / (4 * Real.pi)) / Real.sqrt K
        = ((K : ℝ) / 2) * (1 / (2 * Real.pi * (K : ℝ) * Real.sqrt K)) := by
          have h1 : (K : ℝ) ≠ 0 := hK_pos.ne'
          have h2 : Real.sqrt K ≠ 0 := (Real.sqrt_pos.mpr hK_pos).ne'
          have h3 : Real.pi ≠ 0 := Real.pi_pos.ne'
          field_simp; norm_num
      _ ≤ (S.card : ℝ) * (1 / (2 * Real.pi * (K : ℝ) * Real.sqrt K)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
  exact hfinal.trans (hsum_card.trans hsum_ge)

/-! ### Part 4: Bit-Encoding Injectivity, `‖bandKet‖ = 1`, and `bandSlice53` Approximation -/

lemma bitsToNat_natToBits {q k : ℕ} (hk : k < 2 ^ q) :
    bitsToNat (natToBits q k) = k := by
  rw [← bitsEquivFin_apply]
  simp only [natToBits, Equiv.apply_symm_apply, Fin.val_mk]
  exact Nat.mod_eq_of_lt hk

lemma natToBits_bitsToNat {q : ℕ} (b : Qubits q) :
    natToBits q (bitsToNat b) = b := by
  have hlt : bitsToNat b < 2 ^ q := by
    rw [← bitsEquivFin_apply]
    exact (bitsEquivFin q b).isLt
  have heq : (⟨bitsToNat b % 2 ^ q, Nat.mod_lt _ (Nat.two_pow_pos q)⟩ : Fin (2 ^ q)) = bitsEquivFin q b := by
    ext; simp only [Nat.mod_eq_of_lt hlt, bitsEquivFin_apply]
  calc natToBits q (bitsToNat b)
      = (bitsEquivFin q).symm ⟨bitsToNat b % 2 ^ q, Nat.mod_lt _ (Nat.two_pow_pos q)⟩ := rfl
    _ = (bitsEquivFin q).symm (bitsEquivFin q b) := congrArg (bitsEquivFin q).symm heq
    _ = b := (bitsEquivFin q).symm_apply_apply b

lemma splitReg_flatReg {n q : ℕ} (x : Fin n → Qubits q) (i : Fin n) :
    splitReg n q (flatReg n q x) i = x i := by
  ext j; simp [splitReg, flatReg]

lemma flatReg_splitReg {n q : ℕ} (z : Qubits (n * q)) :
    flatReg n q (splitReg n q z) = z := by
  ext k
  simp only [flatReg, splitReg]
  exact congrArg z (finProdFinEquiv.apply_symm_apply k)

lemma flatReg_natToBits_inj {n q D : ℕ} (hDq : D ≤ 2 ^ q) :
    Function.Injective (fun α : Fin n → Fin D => flatReg n q fun i => natToBits q (α i)) := by
  intro α β h
  dsimp only at h
  ext i
  have h2 : splitReg n q (flatReg n q fun j => natToBits q (α j)) i =
      splitReg n q (flatReg n q fun j => natToBits q (β j)) i := by rw [h]
  rw [splitReg_flatReg, splitReg_flatReg] at h2
  have h3 := congrArg bitsToNat h2
  rwa [bitsToNat_natToBits (lt_of_lt_of_le (α i).isLt hDq),
    bitsToNat_natToBits (lt_of_lt_of_le (β i).isLt hDq)] at h3

lemma sum_ite_eq_apply {A B : Type*} [Fintype A] [DecidableEq B]
    (enc : A → B) (henc : Function.Injective enc) (P : A → Prop) [DecidablePred P]
    (g : A → ℂ) (α : A) :
    (∑ β : A, if enc α = enc β ∧ P β then g β else 0) = if P α then g α else 0 := by
  rw [Finset.sum_eq_single α]
  · simp
  · intro β _ hβα
    have hne : enc α ≠ enc β := fun h => hβα (henc h).symm
    simp [hne]
  · intro h; exact absurd (Finset.mem_univ α) h

lemma norm_sq_toLp_sum_ite {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (enc : A → B) (henc : Function.Injective enc) (P : A → Prop) [DecidablePred P]
    (g : A → ℂ) :
    ‖(WithLp.toLp 2 fun z : B => ∑ α : A, if z = enc α ∧ P α then g α else 0 : EuclideanSpace ℂ B)‖ ^ 2 =
      ∑ α : A, if P α then ‖g α‖ ^ 2 else 0 := by
  rw [PiLp.norm_sq_eq_of_L2]
  let S : Finset A := Finset.univ.filter P
  have hsplit : (Finset.univ : Finset B) = S.image enc ∪ (Finset.univ \ S.image enc) := by
    ext z; simp
  have hdisj : Disjoint (S.image enc) (Finset.univ \ S.image enc) := disjoint_sdiff_self_right
  have himg_zero : ∀ z ∈ Finset.univ \ S.image enc,
      ‖(WithLp.toLp 2 fun w : B => ∑ α : A, if w = enc α ∧ P α then g α else 0 : EuclideanSpace ℂ B) z‖ ^ 2 = 0 := by
    intro z hz
    rw [Finset.mem_sdiff, Finset.mem_image] at hz
    have hsum0 : (∑ α : A, if z = enc α ∧ P α then g α else 0) = 0 := by
      refine Finset.sum_eq_zero fun α _ => ?_
      split_ifs with h
      · exfalso; apply hz.2; exact ⟨α, Finset.mem_filter.mpr ⟨Finset.mem_univ α, h.2⟩, h.1.symm⟩
      · rfl
    change ‖∑ α : A, if z = enc α ∧ P α then g α else 0‖ ^ 2 = 0
    rw [hsum0, norm_zero, sq, mul_zero]
  rw [hsplit, Finset.sum_union hdisj, Finset.sum_eq_zero himg_zero, add_zero]
  rw [Finset.sum_image (fun α _ β _ h => henc h)]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hP : P α := (Finset.mem_filter.mp hα).2
  change ‖∑ β : A, if enc α = enc β ∧ P β then g β else 0‖ ^ 2 = _
  rw [sum_ite_eq_apply enc henc P g α, if_pos hP]

lemma bandWeight_pos_of_norm_eq_one {n K : ℕ} (hK : 1 ≤ K) (w : E n) (hw : ‖w‖ = 1) :
    0 < bandWeight w K := by
  rw [bandWeight_eq_bandWeight_one w hw]
  have hlow := (bandWeight_one_bounds K hK).1
  have hK_pos : (0 : ℝ) < K := by exact_mod_cast hK
  have hpos : 0 < (1 / (4 * Real.pi)) / Real.sqrt K := by positivity
  exact hpos.trans_le hlow

lemma bandKet_norm_eq_one {n K D q : ℕ} (hK : 1 ≤ K) (hKD : 2 * K + 1 ≤ D) (hDq : D ≤ 2 ^ q)
    (w : E n) (hw : ‖w‖ = 1) :
    ‖bandKet n q K w‖ = 1 := by
  have hbw_pos : 0 < bandWeight w K := bandWeight_pos_of_norm_eq_one hK w hw
  have hKq : 2 * K + 1 ≤ 2 ^ q := hKD.trans hDq
  let enc : (Fin n → Fin (2 * K + 1)) → Qubits (n * q) :=
    fun α => flatReg n q fun i => natToBits q (α i)
  have henc : Function.Injective enc := flatReg_natToBits_inj hKq
  let P : (Fin n → Fin (2 * K + 1)) → Prop := fun α => K ≤ ∑ i, (α i : ℕ) ∧ ∑ i, (α i : ℕ) ≤ 2 * K
  let g : (Fin n → Fin (2 * K + 1)) → ℂ :=
    fun α => ((hermCoeff w (fun i => (α i : ℕ)) / Real.sqrt (bandWeight w K) : ℝ) : ℂ)
  have hsq : ‖bandKet n q K w‖ ^ 2 = 1 := by
    change ‖(WithLp.toLp 2 fun z => ∑ α : Fin n → Fin (2 * K + 1),
        if z = enc α ∧ P α then g α else 0 : EuclideanSpace ℂ (Qubits (n * q)))‖ ^ 2 = 1
    rw [norm_sq_toLp_sum_ite enc henc P g]
    have hterm : ∀ α : Fin n → Fin (2 * K + 1),
        (if P α then ‖g α‖ ^ 2 else 0) =
          (if P α then hermCoeff w (fun i => (α i : ℕ)) ^ 2 else 0) / bandWeight w K := by
      intro α
      split_ifs
      · simp only [g, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hbw_pos.le]
      · simp
    simp_rw [hterm, ← Finset.sum_div]
    change bandWeight w K / bandWeight w K = 1
    exact div_self hbw_pos.ne'
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, one_pow, hsq]

lemma bandSlice53_sub_bandKet_le_projDist {n K D q a : ℕ}
    (hK : 1 ≤ K) (hKD : 2 * K + 1 ≤ D) (hDq : D ≤ 2 ^ q)
    (w : E n) (hw : ‖w‖ = 1) (Fw : EuclideanSpace ℂ (Qubits (n * q + a))) :
    ‖bandSlice53 n q a K Fw - (Real.sqrt (bandWeight w K) : ℂ) • bandKet n q K w‖ ≤
      projDist n q a D w Fw := by
  have hbw_pos : 0 < bandWeight w K := bandWeight_pos_of_norm_eq_one hK w hw
  have hsqrt_ne : Real.sqrt (bandWeight w K) ≠ 0 := (Real.sqrt_pos.mpr hbw_pos).ne'
  have hKq : 2 * K + 1 ≤ 2 ^ q := hKD.trans hDq
  let enc : (Fin n → Fin (2 * K + 1)) → Qubits (n * q) :=
    fun α => flatReg n q fun i => natToBits q (α i)
  have henc : Function.Injective enc := flatReg_natToBits_inj hKq
  let P : (Fin n → Fin (2 * K + 1)) → Prop := fun α => K ≤ ∑ i, (α i : ℕ) ∧ ∑ i, (α i : ℕ) ≤ 2 * K
  let d : (Fin n → Fin (2 * K + 1)) → ℂ := fun α =>
    Fw (Fin.append (enc α) (fun _ : Fin a => false)) - (hermCoeff w (fun i => (α i : ℕ)) : ℂ)
  have hsub_eq : bandSlice53 n q a K Fw - (Real.sqrt (bandWeight w K) : ℂ) • bandKet n q K w =
      WithLp.toLp 2 fun z => ∑ α : Fin n → Fin (2 * K + 1), if z = enc α ∧ P α then d α else 0 := by
    ext z
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, bandSlice53, bandKet,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    change (∑ α : Fin n → Fin (2 * K + 1),
        ((if z = enc α ∧ P α then Fw (Fin.append (enc α) (fun _ : Fin a => false)) else 0) -
          (Real.sqrt (bandWeight w K) : ℂ) *
            if z = enc α ∧ P α then ((hermCoeff w (fun i => (α i : ℕ)) / Real.sqrt (bandWeight w K) : ℝ) : ℂ)
            else 0)) =
        ∑ α : Fin n → Fin (2 * K + 1), if z = enc α ∧ P α then d α else 0
    refine Finset.sum_congr rfl fun α _ => ?_
    split_ifs
    · have hmul : (Real.sqrt (bandWeight w K) : ℂ) *
          ((hermCoeff w (fun i => (α i : ℕ)) / Real.sqrt (bandWeight w K) : ℝ) : ℂ) =
          (hermCoeff w (fun i => (α i : ℕ)) : ℂ) := by
        rw [← Complex.ofReal_mul, mul_div_cancel₀ _ hsqrt_ne]
      dsimp [d, enc]
      rw [hmul]
    · simp
  have hnorm_sq :
      ‖bandSlice53 n q a K Fw - (Real.sqrt (bandWeight w K) : ℂ) • bandKet n q K w‖ ^ 2 ≤
        projDist n q a D w Fw ^ 2 := by
    rw [hsub_eq, norm_sq_toLp_sum_ite enc henc P d]
    have hle1 : (∑ α : Fin n → Fin (2 * K + 1), if P α then ‖d α‖ ^ 2 else 0) ≤
        ∑ α : Fin n → Fin (2 * K + 1), ‖d α‖ ^ 2 := by
      refine Finset.sum_le_sum fun α _ => ?_
      split_ifs <;> [exact le_rfl; exact sq_nonneg _]
    let emb : (Fin n → Fin (2 * K + 1)) ↪ (Fin n → Fin D) :=
      ⟨fun α i => Fin.castLE hKD (α i), fun α β h => by
        ext i; exact congrArg (@Fin.val D) (congrFun h i)⟩
    have hle2 : (∑ α : Fin n → Fin (2 * K + 1), ‖d α‖ ^ 2) ≤
        ∑ β : Fin n → Fin D,
          ‖Fw (Fin.append (flatReg n q fun i => natToBits q (β i)) (fun _ : Fin a => false)) -
            (hermCoeff w (fun i => (β i : ℕ)) : ℂ)‖ ^ 2 := by
      have himg : (∑ α : Fin n → Fin (2 * K + 1), ‖d α‖ ^ 2) =
          ∑ β ∈ (Finset.univ : Finset (Fin n → Fin (2 * K + 1))).map emb,
            ‖Fw (Fin.append (flatReg n q fun i => natToBits q (β i)) (fun _ : Fin a => false)) -
              (hermCoeff w (fun i => (β i : ℕ)) : ℂ)‖ ^ 2 := by
        rw [Finset.sum_map]
        refine Finset.sum_congr rfl fun α _ => rfl
      rw [himg]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
    have hproj_sq : projDist n q a D w Fw ^ 2 = ∑ β : Fin n → Fin D,
        ‖Fw (Fin.append (flatReg n q fun i => natToBits q (β i)) (fun _ : Fin a => false)) -
          (hermCoeff w (fun i => (β i : ℕ)) : ℂ)‖ ^ 2 := by
      unfold projDist
      exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    rw [hproj_sq]
    exact hle1.trans hle2
  exact le_of_sq_le_sq hnorm_sq (by unfold projDist; exact Real.sqrt_nonneg _)

lemma bandSlice53_eq_ite_deg {n q a K : ℕ} (hKq : 2 * K + 1 ≤ 2 ^ q)
    (F : EuclideanSpace ℂ (Qubits (n * q + a))) (z : Qubits (n * q)) :
    bandSlice53 n q a K F z =
      if K ≤ ∑ i : Fin n, bitsToNat (splitReg n q z i) ∧
          ∑ i : Fin n, bitsToNat (splitReg n q z i) ≤ 2 * K
      then F (Fin.append z (fun _ : Fin a => false))
      else 0 := by
  let enc : (Fin n → Fin (2 * K + 1)) → Qubits (n * q) :=
    fun α => flatReg n q fun i => natToBits q (α i)
  have henc : Function.Injective enc := flatReg_natToBits_inj hKq
  let P : (Fin n → Fin (2 * K + 1)) → Prop := fun α => K ≤ ∑ i, (α i : ℕ) ∧ ∑ i, (α i : ℕ) ≤ 2 * K
  change (∑ α : Fin n → Fin (2 * K + 1),
      if z = enc α ∧ P α then F (Fin.append (enc α) (fun _ : Fin a => false)) else 0) = _
  by_cases hz : K ≤ ∑ i : Fin n, bitsToNat (splitReg n q z i) ∧
      ∑ i : Fin n, bitsToNat (splitReg n q z i) ≤ 2 * K
  · rw [if_pos hz]
    have hcoord : ∀ i : Fin n, bitsToNat (splitReg n q z i) < 2 * K + 1 := fun i => by
      have hle := Finset.single_le_sum (fun j _ => Nat.zero_le (bitsToNat (splitReg n q z j)))
        (Finset.mem_univ i)
      omega
    let α₀ : Fin n → Fin (2 * K + 1) := fun i => ⟨bitsToNat (splitReg n q z i), hcoord i⟩
    have hencα₀ : enc α₀ = z := by
      dsimp [enc, α₀]
      simp_rw [natToBits_bitsToNat]
      exact flatReg_splitReg z
    have hPα₀ : P α₀ := hz
    rw [← hencα₀, sum_ite_eq_apply enc henc P (fun α => F (Fin.append (enc α) (fun _ : Fin a => false))) α₀,
      if_pos hPα₀, hencα₀]
  · rw [if_neg hz]
    refine Finset.sum_eq_zero fun α _ => ?_
    split_ifs with h
    · exfalso
      apply hz
      have hbits : ∀ i : Fin n, bitsToNat (splitReg n q z i) = (α i : ℕ) := fun i => by
        rw [h.1]
        dsimp [enc]
        rw [splitReg_flatReg, bitsToNat_natToBits (lt_of_lt_of_le (α i).isLt hKq)]
      simpa [hbits] using h.2
    · rfl

lemma flatReg_natToBits_band_iff {n q D K : ℕ} (hKD : 2 * K + 1 ≤ D) (hDq : D ≤ 2 ^ q)
    (z : Qubits (n * q)) :
    (K ≤ ∑ i : Fin n, bitsToNat (splitReg n q z i) ∧
        ∑ i : Fin n, bitsToNat (splitReg n q z i) ≤ 2 * K) ↔
      ∃ α : Fin n → Fin D, z = flatReg n q (fun i => natToBits q (α i)) ∧
        K ≤ ∑ i, (α i : ℕ) ∧ ∑ i, (α i : ℕ) ≤ 2 * K := by
  constructor
  · intro hz
    have hcoord : ∀ i : Fin n, bitsToNat (splitReg n q z i) < D := fun i => by
      have hle := Finset.single_le_sum (fun j _ => Nat.zero_le (bitsToNat (splitReg n q z j)))
        (Finset.mem_univ i)
      omega
    refine ⟨fun i => ⟨bitsToNat (splitReg n q z i), hcoord i⟩, ?_, hz⟩
    simp_rw [natToBits_bitsToNat]
    exact (flatReg_splitReg z).symm
  · rintro ⟨α, rfl, hband⟩
    have hbits : ∀ i : Fin n, bitsToNat (splitReg n q (flatReg n q fun j => natToBits q (α j)) i) =
        (α i : ℕ) := fun i => by
      rw [splitReg_flatReg, bitsToNat_natToBits (lt_of_lt_of_le (α i).isLt hDq)]
    simpa [hbits] using hband


end Aux_w_53_hermite

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

theorem solution :
    (∃ c_band : ℝ, 0 < c_band ∧
      (∀ K : ℕ, 1 ≤ K → c_band / Real.sqrt K ≤ p1D53 K ∧ p1D53 K ≤ 1) ∧
      (∀ (n K : ℕ) (w : EuclideanSpace ℝ (Fin n)), ‖w‖ = 1 → bandWeight w K = p1D53 K)) ∧
    (∀ (n K D q a : ℕ), 1 ≤ K → 2 * K + 1 ≤ D → D ≤ 2 ^ q →
      ∀ (w : EuclideanSpace ℝ (Fin n)), ‖w‖ = 1 →
      ∀ (Fw : EuclideanSpace ℂ (Qubits (n * q + a))),
        ‖bandKet n q K w‖ = 1 ∧
        ‖bandSlice53 n q a K Fw - (Real.sqrt (bandWeight w K) : ℂ) • bandKet n q K w‖ ≤
          projDist n q a D w Fw) ∧
    (∀ (n q a K : ℕ), 2 * K + 1 ≤ 2 ^ q →
      ∀ (F : EuclideanSpace ℂ (Qubits (n * q + a))) (z : Qubits (n * q)),
        bandSlice53 n q a K F z =
          if K ≤ ∑ i : Fin n, bitsToNat (splitReg n q z i) ∧
              ∑ i : Fin n, bitsToNat (splitReg n q z i) ≤ 2 * K
          then F (Fin.append z (fun _ : Fin a => false))
          else 0) ∧
    (∀ (n q D K : ℕ), 2 * K + 1 ≤ D → D ≤ 2 ^ q →
      ∀ z : Qubits (n * q),
        (K ≤ ∑ i : Fin n, bitsToNat (splitReg n q z i) ∧
            ∑ i : Fin n, bitsToNat (splitReg n q z i) ≤ 2 * K) ↔
          ∃ α : Fin n → Fin D, z = flatReg n q (fun i => natToBits q (α i)) ∧
            K ≤ ∑ i, (α i : ℕ) ∧ ∑ i, (α i : ℕ) ≤ 2 * K) := by
  refine ⟨⟨1 / (4 * Real.pi), by positivity, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro K hK
    exact Aux_w_53_hermite.bandWeight_one_bounds K hK
  · intro n K w hw
    exact Aux_w_53_hermite.bandWeight_eq_bandWeight_one w hw
  · intro n K D q a hK hKD hDq w hw Fw
    exact ⟨Aux_w_53_hermite.bandKet_norm_eq_one hK hKD hDq w hw,
      Aux_w_53_hermite.bandSlice53_sub_bandKet_le_projDist hK hKD hDq w hw Fw⟩
  · intro n q a K hKq F z
    exact Aux_w_53_hermite.bandSlice53_eq_ite_deg hKq F z
  · intro n q D K hKD hDq z
    exact Aux_w_53_hermite.flatReg_natToBits_band_iff hKD hDq z
