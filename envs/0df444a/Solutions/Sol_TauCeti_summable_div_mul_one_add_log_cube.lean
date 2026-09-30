-- Prove2me | solution 1 for TauCeti.summable_div_mul_one_add_log_cube
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:31:56.259163+00:00
-- url     : https://prove2.me/submissions/63776f2a-ec60-41ba-aba3-af6f7c6b0648

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_AbelSummation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.AbelSummation
import Theorems.Thm_TauCeti_integrableAtFilter_inv_mul_one_add_log_sq

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Consequences of Abel summation for partial sums

Mathlib's `Mathlib/NumberTheory/AbelSummation.lean` proves the summation-by-parts identity
`∑_{k ≤ x} f k c k = f x ∑_{k ≤ x} c k - ∫ f' (t) ∑_{k ≤ t} c k dt` and derives convergence
criteria from it. This file draws two further consequences from a growth hypothesis on the
partial sums `∑_{1 ≤ k ≤ t} c k`.

* **A logarithmic weight.** Mathlib's `summable_mul_of_bigO_atTop'` converts a bound on the partial
  sums of a sequence into the convergence of a weighted series, provided the weight is
  differentiable and the derivative of the weight against the partial sums admits an integrable
  majorant. This file performs that conversion once, for the weight `(t (1 + log t) ^ 3)⁻¹` and
  partial sums growing like `t log t`. The weight is written with `1 + log t` rather than `log t`
  so that it stays positive and smooth at `t = 1`, where Abel summation starts. Its derivative
  against an `O(t log t)` partial sum is `O((t (1 + log t) ^ 2)⁻¹)`, which is integrable at
  infinity by comparison with Mathlib's log-Cauchy density
  `integrableOn_Ioi_zero_inv_mul_one_add_log_sq`.
* **A power weight.** If the partial sums grow like `κ x`, then the partial sums weighted by
  `n ^ τ`, for an exponent `τ > -1`, grow like `κ x ^ (τ + 1) / (τ + 1)`. This is the step that
  moves a Tauberian conclusion for the coefficients `a n n ^ (1 - σ)` back to the coefficients
  `a n`.

## Main declarations

* `TauCeti.summable_div_mul_one_add_log_cube`: if the partial sums `∑_{1 ≤ k ≤ t} u k` of a
  nonnegative sequence are `O(t log t)`, then `∑ u n / (n (1 + log n) ^ 3)` converges.
* `TauCeti.sum_Icc_rpow_mul_eq`: the exact Abel-summation identity for the weight `t ^ τ`.
* `TauCeti.tendsto_rpow_inv_mul_sum_Icc_rpow_mul`: if `x⁻¹ ∑_{1 ≤ n ≤ x} c n → κ`, then
  `(x ^ (τ + 1))⁻¹ ∑_{1 ≤ n ≤ x} n ^ τ c n → κ / (τ + 1)` for `τ > -1`.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open Asymptotics Filter MeasureTheory Set
open scoped Topology

variable {t : ℝ}

/-! ### The comparison weight -/



/-- `1 + log t` is positive to the right of `exp (-1)`, so the comparison weight is positive on a
neighbourhood of `Ici 1`. -/
private lemma TauCeti.one_add_log_pos (ht : _root_.Real.exp (-1) < t) : 0 < 1 + _root_.Real.log t := by
  have h := _root_.Real.log_lt_log (_root_.Real.exp_pos _) ht
  rw [_root_.Real.log_exp] at h
  linarith

private lemma TauCeti.exp_neg_one_lt_one : _root_.Real.exp (-1) < 1 :=
  _root_.Real.exp_lt_one_iff.2 (by norm_num)

private lemma TauCeti.decayWeight_pos (ht : _root_.Real.exp (-1) < t) : 0 < _root_.TauCeti.decayWeight t := by
  have h := _root_.TauCeti.one_add_log_pos ht
  have ht0 : (0 : ℝ) < t := _root_.lt_trans (_root_.Real.exp_pos _) ht
  exact _root_.inv_pos.2 (by positivity)

private lemma TauCeti.hasDerivAt_decayWeight (ht : _root_.Real.exp (-1) < t) :
    _root_.HasDerivAt _root_.TauCeti.decayWeight
      (-(((1 + _root_.Real.log t) ^ 3 + 3 * (1 + _root_.Real.log t) ^ 2) /
        (t * (1 + _root_.Real.log t) ^ 3) ^ 2)) t := by
  have hlog := _root_.TauCeti.one_add_log_pos ht
  have ht0 : (0 : ℝ) < t := _root_.lt_trans (_root_.Real.exp_pos _) ht
  have ht0' : t ≠ 0 := ht0.ne'
  have hlog' : (1 : ℝ) + _root_.Real.log t ≠ 0 := hlog.ne'
  have h1 : _root_.HasDerivAt (fun u : ℝ ↦ 1 + _root_.Real.log u) t⁻¹ t :=
    (_root_.Real.hasDerivAt_log ht0').const_add 1
  refine ((_root_.hasDerivAt_id' (x := t)).fun_mul (h1.fun_pow 3) |>.inv
    (by positivity)).congr_deriv ?_
  push_cast
  field_simp

/-- On a neighbourhood of `Ici 1` the comparison weight is positive, so taking its norm changes
nothing. -/
private lemma TauCeti.norm_decayWeight_eventuallyEq (ht : 1 ≤ t) :
    (fun u : ℝ ↦ ‖_root_.TauCeti.decayWeight u‖) =ᶠ[𝓝 t] _root_.TauCeti.decayWeight := by
  have hmem : t ∈ _root_.Set.Ioi (_root_.Real.exp (-1)) := _root_.lt_of_lt_of_le _root_.TauCeti.exp_neg_one_lt_one ht
  filter_upwards [isOpen_Ioi.mem_nhds hmem] with u hu
  exact _root_.Real.norm_of_nonneg (_root_.TauCeti.decayWeight_pos hu).le

private lemma TauCeti.differentiableAt_norm_decayWeight (ht : 1 ≤ t) :
    _root_.DifferentiableAt ℝ (fun u : ℝ ↦ ‖_root_.TauCeti.decayWeight u‖) t :=
  (_root_.TauCeti.norm_decayWeight_eventuallyEq ht).differentiableAt_iff.2
    (_root_.TauCeti.hasDerivAt_decayWeight (_root_.lt_of_lt_of_le _root_.TauCeti.exp_neg_one_lt_one ht)).differentiableAt

private lemma TauCeti.deriv_norm_decayWeight (ht : 1 ≤ t) :
    _root_.deriv (fun u : ℝ ↦ ‖_root_.TauCeti.decayWeight u‖) t =
      -(((1 + _root_.Real.log t) ^ 3 + 3 * (1 + _root_.Real.log t) ^ 2) /
        (t * (1 + _root_.Real.log t) ^ 3) ^ 2) := by
  rw [(_root_.TauCeti.norm_decayWeight_eventuallyEq ht).deriv_eq]
  exact (_root_.TauCeti.hasDerivAt_decayWeight (_root_.lt_of_lt_of_le _root_.TauCeti.exp_neg_one_lt_one ht)).deriv

private lemma TauCeti.locallyIntegrableOn_deriv_norm_decayWeight :
    _root_.MeasureTheory.LocallyIntegrableOn (_root_.deriv fun u : ℝ ↦ ‖_root_.TauCeti.decayWeight u‖) (_root_.Set.Ici 1) := by
  refine _root_.ContinuousOn.locallyIntegrableOn ?_ _root_.measurableSet_Ici
  have hne : ∀ u ∈ _root_.Set.Ici (1 : ℝ), u ≠ 0 := fun u hu ↦ by
    have : (1 : ℝ) ≤ u := hu
    linarith
  have hlog : ∀ u ∈ _root_.Set.Ici (1 : ℝ), 1 + _root_.Real.log u ≠ 0 := fun u hu ↦ by
    have : (1 : ℝ) ≤ u := hu
    exact (_root_.TauCeti.one_add_log_pos (_root_.lt_of_lt_of_le _root_.TauCeti.exp_neg_one_lt_one this)).ne'
  refine _root_.ContinuousOn.congr (f := fun u : ℝ ↦
    -(((1 + _root_.Real.log u) ^ 3 + 3 * (1 + _root_.Real.log u) ^ 2) / (u * (1 + _root_.Real.log u) ^ 3) ^ 2)) ?_
    fun u hu ↦ _root_.TauCeti.deriv_norm_decayWeight hu
  have hcont : _root_.ContinuousOn (fun u : ℝ ↦ 1 + _root_.Real.log u) (_root_.Set.Ici 1) :=
    continuousOn_const.add (Real.continuousOn_log.comp _root_.continuousOn_id fun u hu ↦ hne u hu)
  refine (((hcont.pow 3).add ((hcont.pow 2).const_smul (3 : ℝ))).div
    ((continuousOn_id.mul (hcont.pow 3)).pow 2) fun u hu ↦ ?_).neg.congr fun u hu ↦ by
      simp [_root_.smul_eq_mul]
  exact _root_.pow_ne_zero 2 (_root_.mul_ne_zero (hne u hu) (_root_.pow_ne_zero 3 (hlog u hu)))

/-! ### The hypotheses of Abel summation -/

/-- The boundedness hypothesis of Abel summation: an `O(t log t)` partial sum times the comparison
weight is bounded, because `log t ≤ (1 + log t) ^ 3` for `t ≥ 1`. -/
private lemma TauCeti.decayWeight_mul_le {C S : ℝ} (ht : 1 ≤ t) (hC : 0 ≤ C)
    (hS : S ≤ C * t * _root_.Real.log t) : _root_.TauCeti.decayWeight t * S ≤ C := by
  have ht0 : (0 : ℝ) < t := _root_.lt_of_lt_of_le _root_.one_pos ht
  have hL : (0 : ℝ) ≤ _root_.Real.log t := _root_.Real.log_nonneg ht
  have hu : (0 : ℝ) < 1 + _root_.Real.log t := by linarith
  have hkey : (t * (1 + _root_.Real.log t) ^ 3)⁻¹ * (C * t * _root_.Real.log t) =
      C * (_root_.Real.log t / (1 + _root_.Real.log t) ^ 3) := by
    field_simp
  have hratio : _root_.Real.log t / (1 + _root_.Real.log t) ^ 3 ≤ 1 := by
    rw [_root_.div_le_one (by positivity)]
    nlinarith [_root_.pow_pos hu 3, _root_.pow_pos hu 2, _root_.sq_nonneg (_root_.Real.log t)]
  rw [_root_.TauCeti.decayWeight]
  calc (t * (1 + _root_.Real.log t) ^ 3)⁻¹ * S
      ≤ (t * (1 + _root_.Real.log t) ^ 3)⁻¹ * (C * t * _root_.Real.log t) :=
        _root_.mul_le_mul_of_nonneg_left hS (by positivity)
    _ = C * (_root_.Real.log t / (1 + _root_.Real.log t) ^ 3) := hkey
    _ ≤ C := by nlinarith

/-- The majorant hypothesis of Abel summation: the derivative of the comparison weight times an
`O(t log t)` partial sum is `O((t (1 + log t) ^ 2)⁻¹)`, because
`log t (4 + log t) ≤ 4 (1 + log t) ^ 2`. -/
private lemma TauCeti.norm_deriv_decayWeight_mul_le {C S : ℝ} (ht : 1 ≤ t) (hC : 0 ≤ C) (hS0 : 0 ≤ S)
    (hS : S ≤ C * t * _root_.Real.log t) :
    ‖-(((1 + _root_.Real.log t) ^ 3 + 3 * (1 + _root_.Real.log t) ^ 2) /
        (t * (1 + _root_.Real.log t) ^ 3) ^ 2) * S‖ ≤
      4 * C * ‖(t * (1 + _root_.Real.log t) ^ 2)⁻¹‖ := by
  have ht0 : (0 : ℝ) < t := _root_.lt_of_lt_of_le _root_.one_pos ht
  have hL : (0 : ℝ) ≤ _root_.Real.log t := _root_.Real.log_nonneg ht
  have hu : (0 : ℝ) < 1 + _root_.Real.log t := by linarith
  have hX : (0 : ℝ) < (1 + _root_.Real.log t) ^ 3 + 3 * (1 + _root_.Real.log t) ^ 2 := by
    have h3 := _root_.pow_pos hu 3
    have h2 := _root_.pow_pos hu 2
    linarith
  have hY : (0 : ℝ) < (t * (1 + _root_.Real.log t) ^ 3) ^ 2 :=
    _root_.pow_pos (_root_.mul_pos ht0 (_root_.pow_pos hu 3)) 2
  have hden : (0 : ℝ) < t * (1 + _root_.Real.log t) ^ 4 := _root_.mul_pos ht0 (_root_.pow_pos hu 4)
  have hdiv : (0 : ℝ) ≤ ((1 + _root_.Real.log t) ^ 3 + 3 * (1 + _root_.Real.log t) ^ 2) /
      (t * (1 + _root_.Real.log t) ^ 3) ^ 2 := _root_.le_of_lt (_root_.div_pos hX hY)
  rw [_root_.Real.norm_eq_abs, _root_.Real.norm_eq_abs, _root_.abs_mul, _root_.abs_neg, _root_.abs_of_nonneg hdiv,
    _root_.abs_of_nonneg hS0, _root_.abs_of_nonneg (by positivity : (0 : ℝ) ≤ (t * (1 + Real.log t) ^ 2)⁻¹)]
  have hkey : ((1 + _root_.Real.log t) ^ 3 + 3 * (1 + _root_.Real.log t) ^ 2) /
      (t * (1 + _root_.Real.log t) ^ 3) ^ 2 * (C * t * _root_.Real.log t) =
        C * _root_.Real.log t * (4 + _root_.Real.log t) / (t * (1 + _root_.Real.log t) ^ 4) := by
    field_simp
    ring
  have hgoal : 4 * C * (t * (1 + _root_.Real.log t) ^ 2)⁻¹ =
      4 * C * (1 + _root_.Real.log t) ^ 2 / (t * (1 + _root_.Real.log t) ^ 4) := by
    field_simp
  calc ((1 + _root_.Real.log t) ^ 3 + 3 * (1 + _root_.Real.log t) ^ 2) /
        (t * (1 + _root_.Real.log t) ^ 3) ^ 2 * S
      ≤ ((1 + _root_.Real.log t) ^ 3 + 3 * (1 + _root_.Real.log t) ^ 2) /
          (t * (1 + _root_.Real.log t) ^ 3) ^ 2 * (C * t * _root_.Real.log t) :=
        _root_.mul_le_mul_of_nonneg_left hS hdiv
    _ = C * _root_.Real.log t * (4 + _root_.Real.log t) / (t * (1 + _root_.Real.log t) ^ 4) := hkey
    _ ≤ 4 * C * (1 + _root_.Real.log t) ^ 2 / (t * (1 + _root_.Real.log t) ^ 4) := by
        gcongr ?_ / _
        nlinarith [_root_.mul_nonneg hC hL, _root_.mul_nonneg hC (_root_.mul_nonneg hL hL)]
    _ = 4 * C * (t * (1 + _root_.Real.log t) ^ 2)⁻¹ := hgoal.symm

/-! ### The weighted series -/

/-- **Abel summation turns an `O(t log t)` growth bound into a convergent series.** If the partial
sums of a nonnegative sequence `u` satisfy `∑_{1 ≤ k ≤ t} u k = O(t log t)`, then
`∑ u n / (n (1 + log n) ^ 3)` converges: summation by parts against the weight
`(t (1 + log t) ^ 3)⁻¹` leaves the integrable majorant `(t (1 + log t) ^ 2)⁻¹`. -/
theorem solution {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n)
    (hgrowth : (fun t : ℝ ↦ ∑ k ∈ _root_.Finset.Icc 1 ⌊t⌋₊, u k) =O[_root_.Filter.atTop] fun t : ℝ ↦ t * _root_.Real.log t) :
    _root_.Summable fun n : ℕ ↦ u n / (n * (1 + _root_.Real.log n) ^ 3) := by
  have hnorm : ∀ k : ℕ, ‖u k‖ = u k := fun k ↦ _root_.Real.norm_of_nonneg (hu k)
  obtain ⟨C, hC⟩ := hgrowth.bound
  have hbound : ∀ᶠ v : ℝ in _root_.Filter.atTop,
      ∑ k ∈ _root_.Finset.Icc 1 ⌊v⌋₊, u k ≤ _root_.Max.max C 0 * v * _root_.Real.log v := by
    filter_upwards [hC, _root_.Filter.eventually_ge_atTop (1 : ℝ)] with v hv hv1
    have h0 : (0 : ℝ) ≤ _root_.Real.log v := _root_.Real.log_nonneg hv1
    have hle : ∑ k ∈ _root_.Finset.Icc 1 ⌊v⌋₊, u k ≤ C * (v * _root_.Real.log v) := by
      rw [_root_.Real.norm_of_nonneg (_root_.Finset.sum_nonneg fun k _ ↦ hu k),
        _root_.Real.norm_of_nonneg (by positivity)] at hv
      exact hv
    nlinarith [_root_.le_max_left C 0, _root_.mul_nonneg (by linarith : (0 : ℝ) ≤ v) h0]
  have hbdd : (fun n : ℕ ↦ ‖_root_.TauCeti.decayWeight n‖ * ∑ k ∈ _root_.Finset.Icc 1 n, ‖u k‖) =O[_root_.Filter.atTop]
      fun _ : ℕ ↦ (1 : ℝ) := by
    refine .of_bound (_root_.Max.max C 0) ?_
    filter_upwards [(_root_.tendsto_natCast_atTop_atTop (R := ℝ)).eventually hbound,
      _root_.Filter.eventually_ge_atTop 1] with n hn hn1
    have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    rw [_root_.Nat.floor_natCast] at hn
    simp only [hnorm, _root_.NormOneClass.norm_one, _root_.mul_one]
    rw [_root_.Real.norm_of_nonneg (_root_.le_of_lt (_root_.TauCeti.decayWeight_pos
      (_root_.lt_of_lt_of_le _root_.TauCeti.exp_neg_one_lt_one hn1')))]
    rw [_root_.Real.norm_of_nonneg (_root_.mul_nonneg (_root_.le_of_lt (_root_.TauCeti.decayWeight_pos
      (_root_.lt_of_lt_of_le _root_.TauCeti.exp_neg_one_lt_one hn1'))) (_root_.Finset.sum_nonneg fun k _ ↦ hu k))]
    exact _root_.TauCeti.decayWeight_mul_le hn1' (_root_.le_max_right C 0) (by linarith [hn])
  have hg1 : (fun v : ℝ ↦ _root_.deriv (fun w : ℝ ↦ ‖_root_.TauCeti.decayWeight w‖) v *
      ∑ k ∈ _root_.Finset.Icc 1 ⌊v⌋₊, ‖u k‖) =O[_root_.Filter.atTop]
        fun v : ℝ ↦ (v * (1 + _root_.Real.log v) ^ 2)⁻¹ := by
    refine .of_bound (4 * _root_.Max.max C 0) ?_
    filter_upwards [hbound, _root_.Filter.eventually_ge_atTop (1 : ℝ)] with v hv hv1
    simp only [hnorm]
    rw [_root_.TauCeti.deriv_norm_decayWeight hv1]
    exact _root_.TauCeti.norm_deriv_decayWeight_mul_le hv1 (_root_.le_max_right C 0)
      (_root_.Finset.sum_nonneg fun k _ ↦ hu k) hv
  have habel : _root_.Summable fun n : ℕ ↦ _root_.TauCeti.decayWeight n * u n :=
    _root_.summable_mul_of_bigO_atTop' (f := _root_.TauCeti.decayWeight) u
      (fun v hv ↦ _root_.TauCeti.differentiableAt_norm_decayWeight hv)
      _root_.TauCeti.locallyIntegrableOn_deriv_norm_decayWeight hbdd hg1
      _root_.TauCeti.integrableAtFilter_inv_mul_one_add_log_sq
  refine habel.congr fun n ↦ ?_
  rw [_root_.TauCeti.decayWeight, _root_.inv_mul_eq_div]

/-! ### Partial sums against a power weight -/







end TauCeti

end
end
