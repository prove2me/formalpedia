-- Prove2me | solution 1 for TauCeti.Real.isLittleO_integral_div_mul_log_sq
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:39:41.981238+00:00
-- url     : https://prove2.me/submissions/18c76b98-da8d-4166-94e1-2d9ec2b3d6cd

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Theorems.Thm_TauCeti_Real_tendsto_integral_inv_log_sq_mul_log_div_atTop

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The logarithmic integral

This file defines the offset logarithmic integral `Li x = ∫ t in 2..x, (log t)⁻¹` and proves the
prime-number-theorem normalisation `Li x ~ x / log x` as `x → ∞`.

The lower endpoint is `2` rather than `0`: the integrand has a nonintegrable singularity at
`t = 1`, so the unshifted `li` exists only as a principal value, while every arithmetic
application compares a prime count with `Li`. The endpoint agrees with the one used by the
partial-summation identities for prime counts, so the two can be combined without a shift of
origin.

The asymptotic is proved from the exact identity
`Li x = x / log x - 2 / log 2 + ∫ t in 2..x, ((log t) ^ 2)⁻¹`,
the fundamental theorem of calculus applied to `t ↦ t / log t`, together with the estimate that
the remaining integral is `o (x / log x)`. Splitting that integral at `√x` bounds it by
`√x / (log 2) ^ 2 + 4 * x / (log x) ^ 2`, and both terms are `o (x / log x)`.

## Main declarations

* `TauCeti.Real.logIntegral` — the offset logarithmic integral.
* `TauCeti.Real.le_logIntegral` — the elementary lower bound `(x - 2) / log x ≤ Li x`.
* `TauCeti.Real.logIntegral_eq_div_log_sub_add` — the antiderivative identity above.
* `TauCeti.Real.logIntegral_isEquivalent_div_log` — `Li x ~ x / log x` at infinity, with the
  quotient form `TauCeti.Real.tendsto_logIntegral_mul_log_div_atTop`.
* `TauCeti.Real.tendsto_div_div_log_of_isLittleO_logIntegral` — an `o (x / log x)` error
  relative to `δ Li x` gives `f x / (x / log x) → δ`.
* `TauCeti.Real.isLittleO_integral_div_mul_log_sq` — for `f` interval integrable above `2` and of
  at most linear growth, `∫ t in 2..x, f t / (t * log t ^ 2)` is `o (x / log x)`.

The auxiliary bounds `TauCeti.Real.integral_inv_log_pow_le` and
`TauCeti.Real.le_integral_inv_log_pow` estimate `∫ t in a..b, ((log t) ^ n)⁻¹` by monotonicity of
the logarithm. They are stated for a general exponent because the identity above needs `n = 2`
while `Li` itself is the case `n = 1`.

## Roadmap role

This is the analytic half of Layer **6.2** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`,
which asks for `Li` together with `Li(x) ∼ x/log x` on the way to the transfer
`ϑ(x) ∼ δx ⟹ π(x) ∼ δ Li(x)` that Layer 10.3 exports as `primeCount_asymptotic_of_primeTheta`.
The weighted-remainder estimate `isLittleO_integral_div_mul_log_sq` is the analytic input to that
transfer: it is what absorbs the integral produced by Abel summation.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 1.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.

Mathlib's `Mathlib/NumberTheory/Chebyshev.lean` carries out this estimate for the rational
Chebyshev function, in `Chebyshev.integral_theta_div_log_sq_isLittleO`; the argument for a general
integrand below follows the same split into a bounded initial segment and a linearly bounded tail.
-/

 section

namespace TauCeti.Real
end TauCeti.Real
section TauCeti.Real
open TauCeti TauCeti.Real

open Asymptotics Filter MeasureTheory Set
open scoped Topology

/-! ### Reciprocal powers of the logarithm -/

/-- Reciprocal powers of the logarithm are continuous to the right of its zero `t = 1`. -/
theorem TauCeti.Real.continuousOn_inv_log_pow (n : ℕ) :
    _root_.ContinuousOn (fun t : ℝ ↦ (_root_.Real.log t ^ n)⁻¹) (_root_.Set.Ioi 1) := by
  have hlog : _root_.ContinuousOn (fun t : ℝ ↦ _root_.Real.log t) (_root_.Set.Ioi 1) :=
    Real.continuousOn_log.mono fun t ht ↦ _root_.ne_of_gt (_root_.lt_trans _root_.one_pos ht)
  exact (hlog.pow n).inv₀ fun t ht ↦ _root_.ne_of_gt (_root_.pow_pos (_root_.Real.log_pos ht) n)

/-- Reciprocal powers of the logarithm are interval integrable on any interval to the right
of `1`. -/
theorem TauCeti.Real.intervalIntegrable_inv_log_pow (n : ℕ) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    _root_.IntervalIntegrable (fun t : ℝ ↦ (_root_.Real.log t ^ n)⁻¹) _root_.MeasureTheory.MeasureSpace.volume a b := by
  refine ((_root_.TauCeti.Real.continuousOn_inv_log_pow n).mono fun t ht ↦ ?_).intervalIntegrable
  rw [_root_.Set.mem_uIcc] at ht
  rcases ht with ht | ht
  · exact _root_.lt_of_lt_of_le ha ht.1
  · exact _root_.lt_of_lt_of_le hb ht.1





/-- The integrand `(log t ^ n)⁻¹` is nonnegative to the right of `1`, so its integral is. -/
theorem TauCeti.Real.integral_inv_log_pow_nonneg (n : ℕ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    0 ≤ ∫ t in a..b, (_root_.Real.log t ^ n)⁻¹ := by
  refine _root_.intervalIntegral.integral_nonneg hab fun t ht ↦ ?_
  have : 0 < _root_.Real.log t := _root_.Real.log_pos (_root_.lt_of_lt_of_le ha ht.1)
  positivity

/-! ### The logarithmic integral -/











/-! ### The asymptotic `Li x ~ x / log x` -/













/-! ### A weighted remainder integral

The integral `∫ t in 2..x, f t / (t * log t ^ 2)` is what Abel summation leaves behind when a
logarithmically weighted counting function is converted into an unweighted one.  It is negligible
on the scale `x / log x` as soon as `f` grows at most linearly. -/

/-- **The Chebyshev scale `x / log x` diverges.**  Equivalently, a constant is `o (x / log x)`. -/
theorem TauCeti.Real.tendsto_div_log_atTop : _root_.Filter.Tendsto (fun x : ℝ ↦ x / _root_.Real.log x) _root_.Filter.atTop _root_.Filter.atTop := by
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  simp only [_root_.id_eq] at hlog
  have h : _root_.Filter.Tendsto (fun x : ℝ ↦ _root_.Real.log x / x) _root_.Filter.atTop (𝓝[>] 0) := by
    refine _root_.tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hlog ?_
    filter_upwards [_root_.Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    exact _root_.div_pos (_root_.Real.log_pos hx) (by linarith)
  exact h.inv_tendsto_nhdsGT_zero.congr fun x ↦ _root_.inv_div _ _

/-- A constant is `o (x / log x)`, because that scale diverges. -/
theorem TauCeti.Real.isLittleO_const_div_log (c : ℝ) :
    (fun _ : ℝ ↦ c) =o[_root_.Filter.atTop] fun x : ℝ ↦ x / _root_.Real.log x :=
  isLittleO_const_left.mpr <| _root_.Or.inr <|
    (tendsto_abs_atTop_atTop.comp _root_.TauCeti.Real.tendsto_div_log_atTop).congr fun _ ↦ (_root_.Real.norm_eq_abs _).symm



/-- `∫ t in 2..x, (log t ^ 2)⁻¹` is `o (x / log x)`; this is
`TauCeti.Real.tendsto_integral_inv_log_sq_mul_log_div_atTop` read as an `IsLittleO`. -/
theorem TauCeti.Real.isLittleO_integral_inv_log_sq :
    (fun x : ℝ ↦ ∫ t in (2 : ℝ)..x, (_root_.Real.log t ^ 2)⁻¹) =o[_root_.Filter.atTop] fun x : ℝ ↦ x / _root_.Real.log x := by
  refine (_root_.Asymptotics.isLittleO_iff_tendsto' ?_).mpr ?_
  · filter_upwards [_root_.Filter.eventually_gt_atTop (2 : ℝ)] with x hx hzero
    exact _root_.absurd hzero (_root_.div_pos (by linarith) (_root_.Real.log_pos (by linarith))).ne'
  · exact tendsto_integral_inv_log_sq_mul_log_div_atTop.congr fun x ↦
      (_root_.div_div_eq_mul_div _ _ _).symm

/-- The weight `(t * log t ^ 2)⁻¹` is continuous to the right of `1`, so it preserves interval
integrability there. -/
theorem TauCeti.Real.intervalIntegrable_div_mul_log_sq {f : ℝ → ℝ} {a b : ℝ} (ha : 1 < a) (hb : 1 < b)
    (hf : _root_.IntervalIntegrable f _root_.MeasureTheory.MeasureSpace.volume a b) :
    _root_.IntervalIntegrable (fun t ↦ f t / (t * _root_.Real.log t ^ 2)) _root_.MeasureTheory.MeasureSpace.volume a b := by
  simp_rw [_root_.div_eq_mul_inv]
  refine hf.mul_continuousOn fun t ht ↦ ?_
  rw [_root_.Set.mem_uIcc] at ht
  have h1 : 1 < t := by rcases ht with h | h; exacts [ha.trans_le h.1, hb.trans_le h.1]
  have h0 : t ≠ 0 := by linarith
  have hne : t * _root_.Real.log t ^ 2 ≠ 0 :=
    (_root_.mul_pos (by linarith) (_root_.pow_pos (_root_.Real.log_pos h1) 2)).ne'
  fun_prop

/-- Splitting at a cutoff `T` beyond which `|f t| ≤ c t`, the weighted integral of `f` is bounded
by its own initial segment plus `c` times the integral of `(log t ^ 2)⁻¹`. -/
private theorem TauCeti.Real.abs_integral_div_mul_log_sq_le {f : ℝ → ℝ} {c T x : ℝ} (hT2 : 2 ≤ T) (hTx : T ≤ x)
    (hc0 : 0 ≤ c) (hf_int : ∀ y, 2 ≤ y → _root_.IntervalIntegrable f _root_.MeasureTheory.MeasureSpace.volume 2 y)
    (hbound : ∀ t, T ≤ t → |f t| ≤ c * t) :
    |∫ t in (2 : ℝ)..x, f t / (t * _root_.Real.log t ^ 2)| ≤
      |∫ t in (2 : ℝ)..T, f t / (t * _root_.Real.log t ^ 2)| +
        c * ∫ t in (2 : ℝ)..x, (_root_.Real.log t ^ 2)⁻¹ := by
  have h2x : (2 : ℝ) ≤ x := hT2.trans hTx
  have hint : _root_.IntervalIntegrable f _root_.MeasureTheory.MeasureSpace.volume T x := (hf_int x h2x).mono_set <| by
    rw [_root_.Set.uIcc_of_le hTx, _root_.Set.uIcc_of_le h2x]; exact _root_.Set.Icc_subset_Icc hT2 _root_.le_rfl
  have htail : |∫ t in T..x, f t / (t * _root_.Real.log t ^ 2)| ≤
      c * ∫ t in T..x, (_root_.Real.log t ^ 2)⁻¹ := by
    calc |∫ t in T..x, f t / (t * _root_.Real.log t ^ 2)|
        ≤ ∫ t in T..x, |f t / (t * _root_.Real.log t ^ 2)| :=
          _root_.intervalIntegral.abs_integral_le_integral_abs hTx
      _ ≤ ∫ t in T..x, c * (_root_.Real.log t ^ 2)⁻¹ := by
          refine _root_.intervalIntegral.integral_mono_on hTx
            (_root_.TauCeti.Real.intervalIntegrable_div_mul_log_sq (by linarith) (by linarith) hint).abs
            ((_root_.TauCeti.Real.intervalIntegrable_inv_log_pow 2 (by linarith) (by linarith)).const_mul c)
            fun t ht ↦ ?_
          have h2t : (2 : ℝ) ≤ t := hT2.trans ht.1
          have hpos : 0 < t * _root_.Real.log t ^ 2 :=
            _root_.mul_pos (by linarith) (_root_.pow_pos (_root_.Real.log_pos (by linarith)) 2)
          rw [_root_.abs_div, _root_.abs_of_pos hpos, _root_.div_le_iff₀ hpos]
          have hrw : c * (_root_.Real.log t ^ 2)⁻¹ * (t * _root_.Real.log t ^ 2) = c * t := by
            have : _root_.Real.log t ≠ 0 := (_root_.Real.log_pos (by linarith)).ne'
            field_simp
          rw [hrw]
          exact hbound t ht.1
      _ = c * ∫ t in T..x, (_root_.Real.log t ^ 2)⁻¹ := _root_.intervalIntegral.integral_const_mul _ _
  have hJ : (∫ t in T..x, (_root_.Real.log t ^ 2)⁻¹) ≤ ∫ t in (2 : ℝ)..x, (_root_.Real.log t ^ 2)⁻¹ := by
    linarith [_root_.TauCeti.Real.integral_inv_log_pow_nonneg 2 _root_.one_lt_two hT2,
      _root_.intervalIntegral.integral_add_adjacent_intervals
        (a := (2 : ℝ)) (b := T) (c := x) (f := fun t : ℝ ↦ (_root_.Real.log t ^ 2)⁻¹)
        (_root_.TauCeti.Real.intervalIntegrable_inv_log_pow 2 _root_.one_lt_two (by linarith))
        (_root_.TauCeti.Real.intervalIntegrable_inv_log_pow 2 (by linarith) (by linarith))]
  rw [← _root_.intervalIntegral.integral_add_adjacent_intervals
    (_root_.TauCeti.Real.intervalIntegrable_div_mul_log_sq _root_.one_lt_two (by linarith) (hf_int T hT2))
    (_root_.TauCeti.Real.intervalIntegrable_div_mul_log_sq (by linarith) (by linarith) hint)]
  calc |(∫ t in (2 : ℝ)..T, f t / (t * _root_.Real.log t ^ 2)) +
          ∫ t in T..x, f t / (t * _root_.Real.log t ^ 2)|
      ≤ |∫ t in (2 : ℝ)..T, f t / (t * _root_.Real.log t ^ 2)| +
          |∫ t in T..x, f t / (t * _root_.Real.log t ^ 2)| := _root_.abs_add_le _ _
    _ ≤ _ := by gcongr; exact htail.trans (_root_.mul_le_mul_of_nonneg_left hJ hc0)

/-- **A linearly bounded integrand leaves a negligible remainder.**  If `f` is interval integrable
above `2` and satisfies `f = O(x)`, then `∫ t in 2..x, f t / (t * log t ^ 2)` is `o (x / log x)`.

For the rational Chebyshev function this is `Chebyshev.integral_theta_div_log_sq_isLittleO`. -/
theorem solution {f : ℝ → ℝ}
    (hf_int : ∀ x, 2 ≤ x → _root_.IntervalIntegrable f _root_.MeasureTheory.MeasureSpace.volume 2 x) (hf : f =O[_root_.Filter.atTop] _root_.id) :
    (fun x : ℝ ↦ ∫ t in (2 : ℝ)..x, f t / (t * _root_.Real.log t ^ 2)) =o[_root_.Filter.atTop]
      fun x : ℝ ↦ x / _root_.Real.log x := by
  -- Choose a cutoff `T ≥ 2` beyond which `|f t| ≤ c * t`.
  obtain ⟨c, hc⟩ := hf.bound
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hc.and (_root_.Filter.eventually_ge_atTop (2 : ℝ)))
  have hT2 : (2 : ℝ) ≤ T := (hT T _root_.le_rfl).2
  have hbound : ∀ t, T ≤ t → |f t| ≤ c * t := fun t ht ↦ by
    have h2t : (2 : ℝ) ≤ t := (hT t ht).2
    simpa [_root_.Real.norm_eq_abs, _root_.abs_of_nonneg (by linarith : (0 : ℝ) ≤ t)] using (hT t ht).1
  have hc0 : 0 ≤ c := by nlinarith [hbound T _root_.le_rfl, _root_.abs_nonneg (f T)]
  -- Both summands of `abs_integral_div_mul_log_sq_le` are `o (x / log x)`.
  have hconst := _root_.TauCeti.Real.isLittleO_const_div_log |∫ t in (2 : ℝ)..T, f t / (t * _root_.Real.log t ^ 2)|
  have hrem : (fun x : ℝ ↦ c * ∫ t in (2 : ℝ)..x, (_root_.Real.log t ^ 2)⁻¹) =o[_root_.Filter.atTop]
      fun x : ℝ ↦ x / _root_.Real.log x := isLittleO_integral_inv_log_sq.const_mul_left c
  rw [_root_.Asymptotics.isLittleO_iff]
  intro ε hε
  filter_upwards [_root_.Filter.eventually_ge_atTop T, hconst.bound (_root_.half_pos hε), hrem.bound (_root_.half_pos hε)]
    with x hx h1 h2
  rw [_root_.Real.norm_eq_abs, _root_.abs_of_nonneg (_root_.abs_nonneg _)] at h1
  rw [_root_.Real.norm_eq_abs, _root_.abs_of_nonneg
    (_root_.mul_nonneg hc0 (_root_.TauCeti.Real.integral_inv_log_pow_nonneg 2 _root_.one_lt_two (hT2.trans hx)))] at h2
  calc ‖∫ t in (2 : ℝ)..x, f t / (t * _root_.Real.log t ^ 2)‖
      = |∫ t in (2 : ℝ)..x, f t / (t * _root_.Real.log t ^ 2)| := _root_.Real.norm_eq_abs _
    _ ≤ _ := _root_.TauCeti.Real.abs_integral_div_mul_log_sq_le hT2 hx hc0 hf_int hbound
    _ ≤ ε / 2 * ‖x / _root_.Real.log x‖ + ε / 2 * ‖x / _root_.Real.log x‖ := _root_.add_le_add h1 h2
    _ = ε * ‖x / _root_.Real.log x‖ := by ring

end TauCeti.Real

end
end
