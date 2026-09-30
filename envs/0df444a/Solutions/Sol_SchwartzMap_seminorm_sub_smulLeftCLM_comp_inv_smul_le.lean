-- Prove2me | solution 1 for SchwartzMap.seminorm_sub_smulLeftCLM_comp_inv_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:17:18.132963+00:00
-- url     : https://prove2.me/submissions/1e492154-52f1-4b0b-ada9-873044c2ef70

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Cutting off a Schwartz function

Let `χ : E → ℝ` be a smooth compactly supported function that equals `1` near the origin. For a
Schwartz function `f`, the truncations `x ↦ χ (R⁻¹ • x) • f x` are smooth and compactly supported,
and they converge to `f` in the Schwartz topology as `R → ∞`. Consequently the smooth compactly
supported functions are dense in `𝓢(E, F)` when `E` is finite-dimensional.

This is how a statement proved for smooth compactly supported test functions is passed to Schwartz
test functions: any quantity controlled by finitely many Schwartz seminorms (for instance a
weighted sup norm of the Fourier transform) is approximated by its values on the truncations.

The estimate is explicit. Suppose `χ = 1` on the ball of radius `r` and `R ≥ 1`. The difference
`f - χ (R⁻¹ • ·) • f` is `(1 - χ (R⁻¹ • ·)) • f`, which vanishes on the ball of radius `r R`.
Expand its `n`-th derivative by the Leibniz rule. The term in which no derivative falls on the
cutoff is supported where `‖x‖ ≥ r R`, so trading one power of `‖x‖` against `(r R)⁻¹` bounds it by
the `(k + 1, n)` seminorm of `f` divided by `r R`. Every other term carries a derivative of
`χ (R⁻¹ • ·)` of order `i ≥ 1`, which is `R⁻ⁱ` times a derivative of `χ` and hence `O(R⁻¹)`.
Altogether the `(k, n)` seminorm of the difference is `O(R⁻¹)`.

## Main results

* `SchwartzMap.seminorm_sub_smulLeftCLM_comp_inv_smul_le`: the explicit bound
  `seminorm k n (f - χ (R⁻¹ • ·) • f) ≤ K / R` for `R ≥ 1`.
* `SchwartzMap.tendsto_smulLeftCLM_comp_inv_smul_atTop`: the truncations converge to `f` in
  `𝓢(E, F)`.
* `SchwartzMap.hasCompactSupport_smulLeftCLM_comp_inv_smul`: the truncations are compactly
  supported.
* `SchwartzMap.dense_hasCompactSupport`: compactly supported functions are dense in
  `𝓢(E, F)` for finite-dimensional `E`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Section 7.1.
-/

 section

open Filter Metric Set
open scoped ContDiff Topology SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

namespace SchwartzMap
end SchwartzMap
section SchwartzMap
open SchwartzMap

variable {χ : E → ℝ}

/-- The truncation `χ (R⁻¹ • ·) • f` of a Schwartz function by a cutoff of temperate growth,
evaluated pointwise. -/
@[simp]
theorem SchwartzMap.smulLeftCLM_comp_inv_smul_apply (hχ : χ.HasTemperateGrowth) (R : ℝ) (f : 𝓢(E, F))
    (x : E) : _root_.SchwartzMap.smulLeftCLM F (fun y ↦ χ (R⁻¹ • y)) f x = χ (R⁻¹ • x) • f x :=
  _root_.SchwartzMap.smulLeftCLM_apply_apply (hχ.comp (R⁻¹ • _root_.ContinuousLinearMap.id ℝ E).hasTemperateGrowth) f x



/-- For `i ≠ 0` and `R ≥ 1`, the `i`-th derivative of `1 - χ (R⁻¹ • ·)` is at most `B / R`, where
`B` bounds the `i`-th derivative of `χ`. -/
private lemma SchwartzMap.norm_iteratedFDeriv_one_sub_comp_inv_smul_le (hχ : _root_.ContDiff ℝ ∞ χ) {i : ℕ}
    (hi : i ≠ 0) {B : ℝ} (hB : ∀ x, ‖_root_.iteratedFDeriv ℝ i χ x‖ ≤ B) {R : ℝ} (hR : 1 ≤ R) (x : E) :
    ‖_root_.iteratedFDeriv ℝ i (fun y ↦ 1 - χ (R⁻¹ • y)) x‖ ≤ B / R := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hcomp : _root_.ContDiff ℝ i fun y ↦ χ (R⁻¹ • y) :=
    (hχ.comp (_root_.contDiff_const_smul _)).of_le (mod_cast _root_.le_top)
  rw [_root_.fun_iteratedFDeriv_sub_apply _root_.contDiffAt_const hcomp.contDiffAt,
    _root_.iteratedFDeriv_const_of_ne hi, _root_.Pi.zero_apply, _root_.zero_sub, _root_.norm_neg,
    _root_.iteratedFDeriv_comp_const_smul _ (hχ.of_le (mod_cast _root_.le_top)), _root_.norm_smul, _root_.norm_pow,
    _root_.norm_inv, _root_.Real.norm_of_nonneg hR0.le]
  have hRi : (R ^ i)⁻¹ ≤ R⁻¹ := by
    rw [← _root_.inv_pow]
    exact _root_.pow_le_of_le_one (by positivity) (_root_.inv_le_one_of_one_le₀ hR) hi
  calc (R⁻¹) ^ i * ‖_root_.iteratedFDeriv ℝ i χ (R⁻¹ • x)‖ ≤ R⁻¹ * B := by
        rw [_root_.inv_pow]
        exact _root_.mul_le_mul hRi (hB _) (_root_.norm_nonneg _) (by positivity)
    _ = B / R := by rw [_root_.inv_mul_eq_div]

/-- Where `‖x‖ ≥ ρ > 0`, one power of `‖x‖` can be traded for `ρ⁻¹` against the next seminorm. -/
private lemma SchwartzMap.pow_mul_norm_iteratedFDeriv_le_div (f : 𝓢(E, F)) (k j : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    {x : E} (hx : ρ ≤ ‖x‖) :
    ‖x‖ ^ k * ‖_root_.iteratedFDeriv ℝ j f x‖ ≤ _root_.SchwartzMap.seminorm ℝ (k + 1) j f / ρ := by
  rw [_root_.le_div_iff₀ hρ]
  calc ‖x‖ ^ k * ‖_root_.iteratedFDeriv ℝ j f x‖ * ρ ≤ ‖x‖ ^ k * ‖_root_.iteratedFDeriv ℝ j f x‖ * ‖x‖ :=
        _root_.mul_le_mul_of_nonneg_left hx (by positivity)
    _ = ‖x‖ ^ (k + 1) * ‖_root_.iteratedFDeriv ℝ j f x‖ := by ring
    _ ≤ _root_.SchwartzMap.seminorm ℝ (k + 1) j f := _root_.SchwartzMap.le_seminorm ℝ (k + 1) j f x

/-- One Leibniz term of `D^n ((1 - χ (R⁻¹ • ·)) • f)` at a point with `‖x‖ ≥ r R` is `O(R⁻¹)`:
if no derivative falls on the cutoff, the factor `‖x‖ ^ k` is traded for `(r R)⁻¹`, and otherwise
the derivative of the cutoff contributes the factor `R⁻¹`. -/
private lemma SchwartzMap.norm_iteratedFDeriv_one_sub_mul_le (hχ : _root_.ContDiff ℝ ∞ χ) {B : ℕ → ℝ}
    (hB : ∀ i x, ‖_root_.iteratedFDeriv ℝ i χ x‖ ≤ B i) {r : ℝ} (hr : 0 < r) (f : 𝓢(E, F))
    (k n i : ℕ) {R : ℝ} (hR : 1 ≤ R) {x : E} (hx : r * R ≤ ‖x‖) :
    ‖_root_.iteratedFDeriv ℝ i (fun y ↦ 1 - χ (R⁻¹ • y)) x‖ *
        (‖x‖ ^ k * ‖_root_.iteratedFDeriv ℝ (n - i) f x‖) ≤
      (1 + B i) * (_root_.SchwartzMap.seminorm ℝ k (n - i) f +
        _root_.SchwartzMap.seminorm ℝ (k + 1) (n - i) f / r) / R := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hB0 : ∀ i, 0 ≤ B i := fun i ↦ (_root_.norm_nonneg _).trans (hB i 0)
  have hrR : 0 < r * R := _root_.mul_pos hr hR0
  rcases _root_.eq_or_ne i 0 with rfl | hi
  · -- No derivative falls on the cutoff: use `‖x‖ ≥ r R`.
    have hh0 : ‖_root_.iteratedFDeriv ℝ 0 (fun y ↦ 1 - χ (R⁻¹ • y)) x‖ ≤ 1 + B 0 := by
      rw [_root_.norm_iteratedFDeriv_zero]
      refine (_root_.norm_sub_le _ _).trans ?_
      have := hB 0 (R⁻¹ • x)
      rw [_root_.norm_iteratedFDeriv_zero] at this
      simpa using this
    have hf0 := _root_.SchwartzMap.pow_mul_norm_iteratedFDeriv_le_div f k (n - 0) hrR hx
    have hS : 0 ≤ _root_.SchwartzMap.seminorm ℝ k (n - 0) f := _root_.NonnegHomClass.apply_nonneg _ _
    calc _ ≤ (1 + B 0) * (_root_.SchwartzMap.seminorm ℝ (k + 1) (n - 0) f / (r * R)) :=
          _root_.mul_le_mul hh0 hf0 (by positivity) (by linarith [hB0 0])
      _ = (1 + B 0) * (_root_.SchwartzMap.seminorm ℝ (k + 1) (n - 0) f / r) / R := by
          field_simp
      _ ≤ _ := by
          gcongr
          · linarith [hB0 0]
          · exact _root_.le_add_of_nonneg_left hS
  · -- A derivative falls on the cutoff: it contributes a factor `R⁻¹`.
    have hhi := _root_.SchwartzMap.norm_iteratedFDeriv_one_sub_comp_inv_smul_le hχ hi (hB i) hR x
    have hfi : ‖x‖ ^ k * ‖_root_.iteratedFDeriv ℝ (n - i) f x‖ ≤
        _root_.SchwartzMap.seminorm ℝ k (n - i) f := _root_.SchwartzMap.le_seminorm ℝ k (n - i) f x
    have hS : 0 ≤ _root_.SchwartzMap.seminorm ℝ (k + 1) (n - i) f / r :=
      _root_.div_nonneg (_root_.NonnegHomClass.apply_nonneg _ _) hr.le
    calc _ ≤ B i / R * _root_.SchwartzMap.seminorm ℝ k (n - i) f :=
          _root_.mul_le_mul hhi hfi (by positivity) (by have := hB0 i; positivity)
      _ ≤ (1 + B i) / R * (_root_.SchwartzMap.seminorm ℝ k (n - i) f +
            _root_.SchwartzMap.seminorm ℝ (k + 1) (n - i) f / r) := by
          gcongr
          · exact _root_.div_nonneg (by linarith [hB0 i]) hR0.le
          · linarith
          · exact _root_.le_add_of_nonneg_right hS
      _ = _ := by ring

/-- **The truncation estimate.** Let `χ` be smooth with `‖D^i χ‖ ≤ B i` for every `i`, and equal
to `1` on the ball of radius `r > 0`. For `R ≥ 1` the `(k, n)` seminorm of `f - χ (R⁻¹ • ·) • f`
is at most `K / R`, where `K` depends on `χ`, `f`, `k` and `n` but not on `R`. -/
theorem solution (hχ : _root_.ContDiff ℝ ∞ χ)
    {B : ℕ → ℝ} (hB : ∀ i x, ‖_root_.iteratedFDeriv ℝ i χ x‖ ≤ B i)
    {r : ℝ} (hr : 0 < r) (hχ1 : ∀ y, ‖y‖ < r → χ y = 1) (f : 𝓢(E, F)) (k n : ℕ) {R : ℝ}
    (hR : 1 ≤ R) :
    _root_.SchwartzMap.seminorm ℝ k n (f - _root_.SchwartzMap.smulLeftCLM F (fun y ↦ χ (R⁻¹ • y)) f) ≤
      (∑ i ∈ _root_.Finset.range (n + 1), (n.choose i : ℝ) * (1 + B i) *
        (_root_.SchwartzMap.seminorm ℝ k (n - i) f + _root_.SchwartzMap.seminorm ℝ (k + 1) (n - i) f / r)) /
        R := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hB0 : ∀ i, 0 ≤ B i := fun i ↦ (_root_.norm_nonneg _).trans (hB i 0)
  set h : E → ℝ := fun y ↦ 1 - χ (R⁻¹ • y) with hh
  have hhsmooth : _root_.ContDiff ℝ ∞ h := contDiff_const.sub (hχ.comp (_root_.contDiff_const_smul _))
  have hcoe : ⇑(f - _root_.SchwartzMap.smulLeftCLM F (fun y ↦ χ (R⁻¹ • y)) f) = fun x ↦ h x • f x := by
    ext x
    have hχt : χ.HasTemperateGrowth := ⟨hχ, fun i ↦ ⟨0, B i, fun x ↦ by simpa using hB i x⟩⟩
    simp only [_root_.sub_apply, _root_.SchwartzMap.smulLeftCLM_comp_inv_smul_apply hχt R f x, hh, _root_.sub_smul, _root_.one_smul]
  have hK : 0 ≤ ∑ i ∈ _root_.Finset.range (n + 1), (n.choose i : ℝ) * (1 + B i) *
      (_root_.SchwartzMap.seminorm ℝ k (n - i) f + _root_.SchwartzMap.seminorm ℝ (k + 1) (n - i) f / r) :=
    _root_.Finset.sum_nonneg fun i _ ↦ _root_.mul_nonneg (_root_.mul_nonneg (_root_.Nat.cast_nonneg _)
      (by linarith [hB0 i])) (_root_.add_nonneg (_root_.NonnegHomClass.apply_nonneg _ _) (_root_.div_nonneg (_root_.NonnegHomClass.apply_nonneg _ _) hr.le))
  refine _root_.SchwartzMap.seminorm_le_bound ℝ k n _ (_root_.div_nonneg hK hR0.le) fun x ↦ ?_
  rw [hcoe]
  rcases _root_.lt_or_ge ‖x‖ (r * R) with hx | hx
  · -- Near the origin the truncation agrees with `f`, so the difference is locally zero.
    have hzero : (fun y ↦ h y • f y) =ᶠ[𝓝 x] 0 := by
      filter_upwards [isOpen_ball.mem_nhds (_root_.mem_ball_zero_iff.2 hx)] with y hy
      rw [_root_.mem_ball_zero_iff] at hy
      have hy' : ‖R⁻¹ • y‖ < r := by
        rw [_root_.norm_smul, _root_.norm_inv, _root_.Real.norm_of_nonneg hR0.le, _root_.inv_mul_lt_iff₀ hR0]
        linarith
      simp [hh, hχ1 _ hy']
    rw [(hzero.iteratedFDeriv ℝ n).eq_of_nhds, _root_.iteratedFDeriv_zero, _root_.Pi.zero_apply,
      _root_.norm_zero, _root_.MulZeroClass.mul_zero]
    exact _root_.div_nonneg hK hR0.le
  · -- Away from the origin, expand by the Leibniz rule and bound each term by `O(R⁻¹)`.
    refine (_root_.mul_le_mul_of_nonneg_left (_root_.norm_iteratedFDeriv_smul_le hhsmooth (f.smooth ⊤) x
      (mod_cast _root_.le_top)) (by positivity)).trans ?_
    rw [_root_.Finset.mul_sum, _root_.Finset.sum_div]
    refine _root_.Finset.sum_le_sum fun i _ ↦ ?_
    calc ‖x‖ ^ k * ((n.choose i : ℝ) * ‖_root_.iteratedFDeriv ℝ i h x‖ *
          ‖_root_.iteratedFDeriv ℝ (n - i) f x‖)
        = (n.choose i : ℝ) *
            (‖_root_.iteratedFDeriv ℝ i h x‖ * (‖x‖ ^ k * ‖_root_.iteratedFDeriv ℝ (n - i) f x‖)) := by ring
      _ ≤ (n.choose i : ℝ) * ((1 + B i) * (_root_.SchwartzMap.seminorm ℝ k (n - i) f +
            _root_.SchwartzMap.seminorm ℝ (k + 1) (n - i) f / r) / R) :=
          _root_.mul_le_mul_of_nonneg_left (_root_.SchwartzMap.norm_iteratedFDeriv_one_sub_mul_le hχ hB hr f k n i hR hx)
            (_root_.Nat.cast_nonneg _)
      _ = _ := by ring





end SchwartzMap

end
end
