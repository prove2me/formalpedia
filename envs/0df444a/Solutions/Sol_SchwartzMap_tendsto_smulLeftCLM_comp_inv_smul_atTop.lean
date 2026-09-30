-- Prove2me | solution 1 for SchwartzMap.tendsto_smulLeftCLM_comp_inv_smul_atTop
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:32:39.235812+00:00
-- url     : https://prove2.me/submissions/0a648c48-491e-4535-8270-4f6350413875

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Theorems.Thm_SchwartzMap_seminorm_sub_smulLeftCLM_comp_inv_smul_le

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













/-- **Truncations converge in the Schwartz topology.** If `χ` is smooth with every derivative
bounded (for instance, if `χ` is compactly supported) and equal to `1` near the origin, then
`χ (R⁻¹ • ·) • f → f` in `𝓢(E, F)` as `R → ∞`. -/
theorem solution (hχ : _root_.ContDiff ℝ ∞ χ)
    (hbdd : ∀ i, ∃ B, ∀ x, ‖_root_.iteratedFDeriv ℝ i χ x‖ ≤ B) (hχ1 : χ =ᶠ[𝓝 0] 1) (f : 𝓢(E, F)) :
    _root_.Filter.Tendsto (fun R : ℝ ↦ _root_.SchwartzMap.smulLeftCLM F (fun y ↦ χ (R⁻¹ • y)) f) _root_.Filter.atTop (𝓝 f) := by
  choose B hB using hbdd
  obtain ⟨r, hr, hχr⟩ := _root_.Metric.eventually_nhds_iff.1 hχ1
  have hχ1' : ∀ y, ‖y‖ < r → χ y = 1 := fun y hy ↦ hχr (by rwa [_root_.dist_zero_right])
  rw [(_root_.schwartz_withSeminorms ℝ E F).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  set K := ∑ i ∈ _root_.Finset.range (n + 1), (n.choose i : ℝ) * (1 + B i) *
    (_root_.SchwartzMap.seminorm ℝ k (n - i) f + _root_.SchwartzMap.seminorm ℝ (k + 1) (n - i) f / r)
  filter_upwards [_root_.Filter.eventually_ge_atTop 1, _root_.Filter.eventually_gt_atTop (K / ε)] with R hR hKR
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  rw [_root_.SchwartzMap.schwartzSeminormFamily_apply, ← _root_.AddGroupSeminormClass.map_neg_eq_map, _root_.neg_sub]
  refine (_root_.SchwartzMap.seminorm_sub_smulLeftCLM_comp_inv_smul_le hχ hB hr hχ1' f k n hR).trans_lt ?_
  rw [_root_.div_lt_iff₀ hR0]
  rwa [_root_.div_lt_iff₀ hε, _root_.mul_comm] at hKR



end SchwartzMap

end
end
