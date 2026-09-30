-- Prove2me | solution 1 for TauCeti.LSeries.LSeriesSummable_mul_of_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:47:59.330278+00:00
-- url     : https://prove2.me/submissions/2159851e-3931-4e83-85f9-46553429443c

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.Basic
import Theorems.Thm_TauCeti_summable_div_mul_one_add_log_cube

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Summability at `s = 1` of a logarithmically damped Dirichlet series

A Dirichlet series whose coefficients have `O(t log t)` partial sums need not converge on the line
`Re s = 1`, but it does converge there once each coefficient is weighted by a factor of size
`O((1 + log n) ^ (-3))`: in the Abel-summation bound
`TauCeti.summable_div_mul_one_add_log_cube`, one of the three logarithms absorbs the `log t` in the
growth of the partial sums, and the remaining two leave the integrable majorant
`(t (1 + log t) ^ 2)⁻¹`.

Such a weight arises whenever a Dirichlet series is tested against a smooth compactly supported
function, whose Fourier transform decays faster than every power.

## Main declarations

* `TauCeti.LSeries.LSeriesSummable_mul_of_norm_le`: an `O((1 + log n) ^ (-3))` weighting of
  coefficients with `O(t log t)` partial sums has a Dirichlet series converging at `s = 1`.
-/

 section

namespace TauCeti.LSeries
end TauCeti.LSeries
section TauCeti.LSeries
open TauCeti TauCeti.LSeries

open Asymptotics Filter

variable {a W : ℕ → ℂ} {D : ℝ}

/-- Weighting coefficients with an `O((1 + log n) ^ (-3))` factor leaves a Dirichlet series that
converges at `s = 1`, as soon as the partial sums of `‖a‖` are `O(t log t)`. -/
theorem solution
    (hgrowth : (fun t : ℝ ↦ ∑ k ∈ _root_.Finset.Icc 1 ⌊t⌋₊, ‖a k‖) =O[_root_.Filter.atTop] fun t : ℝ ↦ t * _root_.Real.log t)
    (hW : ∀ᶠ n : ℕ in _root_.Filter.atTop, ‖W n‖ ≤ D / (1 + _root_.Real.log n) ^ 3) :
    _root_.LSeriesSummable (fun n ↦ a n * W n) 1 := by
  have hD : 0 ≤ D := by
    obtain ⟨n, hn, hn1⟩ := (hW.and (_root_.Filter.eventually_ge_atTop 1)).exists
    have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hu : (0 : ℝ) < 1 + _root_.Real.log n := by
      have := _root_.Real.log_nonneg hn1'
      linarith
    have h0 : (0 : ℝ) ≤ D / (1 + _root_.Real.log n) ^ 3 := _root_.le_trans (_root_.norm_nonneg _) hn
    rwa [_root_.le_div_iff₀ (_root_.pow_pos hu 3), _root_.MulZeroClass.zero_mul] at h0
  refine _root_.Summable.of_norm_bounded_eventually_nat
    (g := fun n : ℕ ↦ D * (‖a n‖ / (n * (1 + _root_.Real.log n) ^ 3)))
    ((_root_.TauCeti.summable_div_mul_one_add_log_cube (fun n ↦ _root_.norm_nonneg (a n)) hgrowth).mul_left D) ?_
  filter_upwards [hW, _root_.Filter.eventually_ge_atTop 1] with n hn hn1
  have hn0 : n ≠ 0 := by omega
  have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hu : (0 : ℝ) < 1 + _root_.Real.log n := by
    have := _root_.Real.log_nonneg hn1'
    linarith
  rw [_root_.LSeries.term_of_ne_zero hn0, _root_.Complex.cpow_one, _root_.norm_div, _root_.norm_mul,
    _root_.Complex.norm_natCast]
  calc ‖a n‖ * ‖W n‖ / (n : ℝ)
      ≤ ‖a n‖ * (D / (1 + _root_.Real.log n) ^ 3) / (n : ℝ) := by gcongr
    _ = D * (‖a n‖ / ((n : ℝ) * (1 + _root_.Real.log n) ^ 3)) := by
        have hn' : (n : ℝ) ≠ 0 := hnpos.ne'
        have hu' : (1 : ℝ) + _root_.Real.log n ≠ 0 := hu.ne'
        field_simp

end TauCeti.LSeries

end
end
