-- Prove2me | solution 1 for TauCeti.LSeries.isBigO_sum_Icc_norm_of_boundary
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:31:58.425342+00:00
-- url     : https://prove2.me/submissions/c2af93c2-a8b8-483c-9bf4-e5b489a15faf

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Deriv
import Theorems.Thm_TauCeti_LSeries_tsum_norm_term_le_of_boundary

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# A growth bound for nonnegative coefficients, and the summability it supplies

The smoothed Wiener--Ikehara asymptotic
`TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop` still carries a summability hypothesis: the
Fourier-weighted series `∑ a n 𝓕 psi (log (n / x) / 2π) / n` has to converge on the boundary line
`Re s = 1`, where the coefficients are no longer damped by `n ^ (-(sigma - 1))`. This file removes
that hypothesis for nonnegative coefficients, which is the only case Wiener--Ikehara is about.

The input is coefficient nonnegativity together with the boundary remainder data on the real
segment `sigma ∈ (1, 2]`; the growth bound for the partial sums is derived from them, not assumed.
Nonnegativity turns the boundary data into the one-sided estimate
`∑ ‖a n‖ / n ^ sigma ≤ B / (sigma - 1)` on `(1, 2]`, and inserting
`sigma = 1 + 1 / log t` into it bounds `∑_{n ≤ t} ‖a n‖` by a multiple of `t log t`. That is weaker
than the Chebyshev bound `O(t)` which Wiener--Ikehara ultimately proves, but it is available before
any Tauberian argument, and one logarithm to spare is all the summability needs: the Fourier
transform of a smooth compactly supported function decays faster than `|v| ^ (-3)`, so the factor
attached to `a n` is `O((log n) ^ (-3))`, and the Abel-summation bound
`TauCeti.LSeries.LSeriesSummable_mul_of_norm_le` converts `O(t log t)` partial sums into a
convergent series.

Only the values of the boundary remainder on the real segment `sigma ∈ (1, 2]` enter the growth
bound, so the results below are stated with the boundary data restricted to that segment; the final
asymptotic specializes the half-plane hypotheses it inherits from
`TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop_of_contDiff`.

## Main results

* `TauCeti.LSeries.tsum_norm_term_le_of_boundary`: nonnegative coefficients with a boundary
  remainder continuous on the segment `[1, 2]` have a convergent norm series with
  `∑ ‖term a sigma n‖ ≤ B / (sigma - 1)` on `(1, 2]`.
* `TauCeti.LSeries.isBigO_sum_Icc_norm_of_boundary`: the resulting `O(t log t)` bound for the
  partial sums.
* `TauCeti.LSeries.LSeriesSummable_mul_fourier_of_nonneg`: the Fourier weight is small enough for
  that bound to force summability at `s = 1`, at every scale `x > 0`.
* `TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop_of_nonneg`: **the smoothed Wiener--Ikehara
  asymptotic for nonnegative coefficients**, with no summability hypothesis left.

## References

* J. Korevaar, *Tauberian Theory: A Century of Developments*, Chapter III.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.
-/

 section

namespace TauCeti.LSeries
end TauCeti.LSeries
section TauCeti.LSeries
open TauCeti TauCeti.LSeries

open Asymptotics Complex Filter FourierTransform MeasureTheory Real Set
open scoped ComplexOrder ContDiff Topology

variable {a : ℕ → ℂ} {A : ℂ} {G : ℂ → ℂ} {psi : ℝ → ℂ} {x : ℝ}

/-! ### The one-sided bound coming from the boundary data -/



/-! ### The partial-sum bound -/

/-- **A crude growth bound for the partial sums.** Nonnegative coefficients whose Dirichlet series
has a boundary remainder continuous on the segment `[1, 2]` satisfy
`∑_{1 ≤ n ≤ t} ‖a n‖ = O(t log t)`.

The proof inserts `sigma = 1 + 1 / log t` into `tsum_norm_term_le_of_boundary`: the truncation
`n ≤ t` costs a factor `t ^ sigma = e t`, and the bound `B / (sigma - 1)` is `B log t`. This is one
logarithm short of the Chebyshev bound `O(t)` that Wiener--Ikehara eventually delivers, but it
needs no Tauberian input. -/
theorem solution (ha : 0 ≤ a)
    (hG : _root_.ContinuousOn (fun sigma : ℝ ↦ G (sigma : ℂ)) (_root_.Set.Icc 1 2))
    (hG' : ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 →
      G (sigma : ℂ) = _root_.LSeries a (sigma : ℂ) - A / ((sigma : ℂ) - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 → _root_.LSeriesSummable a (sigma : ℂ)) :
    (fun t : ℝ ↦ ∑ k ∈ _root_.Finset.Icc 1 ⌊t⌋₊, ‖a k‖) =O[_root_.Filter.atTop] fun t : ℝ ↦ t * _root_.Real.log t := by
  obtain ⟨B, hB0, hB⟩ := _root_.TauCeti.LSeries.tsum_norm_term_le_of_boundary ha hG hG' hsum
  refine .of_bound (_root_.Real.exp 1 * B) ?_
  filter_upwards [_root_.Filter.eventually_ge_atTop (_root_.Real.exp 1)] with t ht
  have ht0 : (0 : ℝ) < t := _root_.lt_of_lt_of_le (_root_.Real.exp_pos 1) ht
  have hlog1 : (1 : ℝ) ≤ _root_.Real.log t := (_root_.Real.le_log_iff_exp_le ht0).2 ht
  have hlogpos : (0 : ℝ) < _root_.Real.log t := by linarith
  set sigma : ℝ := 1 + 1 / _root_.Real.log t with hsig
  have h1 : 1 < sigma := by
    rw [hsig]
    have : (0 : ℝ) < 1 / _root_.Real.log t := by positivity
    linarith
  have h2 : sigma ≤ 2 := by
    rw [hsig]
    have : 1 / _root_.Real.log t ≤ 1 := by rw [_root_.div_le_one hlogpos]; exact hlog1
    linarith
  have hsig1 : sigma - 1 = 1 / _root_.Real.log t := by rw [hsig]; ring
  obtain ⟨hsummable, hbound⟩ := hB sigma h1 h2
  have hpow : t ^ sigma = _root_.Real.exp 1 * t := by
    rw [hsig, _root_.Real.rpow_add ht0, _root_.Real.rpow_one, _root_.Real.rpow_def_of_pos ht0, _root_.mul_one_div,
      _root_.div_self hlogpos.ne']
    ring
  have hfloor : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := _root_.Nat.floor_le ht0.le
  rw [_root_.Real.norm_of_nonneg (_root_.Finset.sum_nonneg fun _ _ ↦ _root_.norm_nonneg _),
    _root_.Real.norm_of_nonneg (by positivity)]
  calc ∑ k ∈ _root_.Finset.Icc 1 ⌊t⌋₊, ‖a k‖
      ≤ ∑ k ∈ _root_.Finset.Icc 1 ⌊t⌋₊, ‖_root_.LSeries.term a (sigma : ℂ) k‖ * t ^ sigma := by
        refine _root_.Finset.sum_le_sum fun k hk ↦ ?_
        obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
        have hk0 : k ≠ 0 := by omega
        have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
        have hknorm : ‖_root_.LSeries.term a (sigma : ℂ) k‖ = ‖a k‖ / (k : ℝ) ^ sigma := by
          rw [_root_.LSeries.term_of_ne_zero hk0, _root_.norm_div, ← _root_.Complex.ofReal_natCast,
            ← _root_.Complex.ofReal_cpow (_root_.Nat.cast_nonneg k), _root_.Complex.norm_real,
            _root_.Real.norm_of_nonneg (by positivity)]
        have hkt : (k : ℝ) ≤ t := _root_.le_trans (_root_.Nat.cast_le.2 hk2) hfloor
        rw [hknorm, _root_.div_mul_eq_mul_div, _root_.le_div_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) ^ sigma)]
        exact _root_.mul_le_mul_of_nonneg_left
          (_root_.Real.rpow_le_rpow (_root_.Nat.cast_nonneg k) hkt (by linarith)) (_root_.norm_nonneg _)
    _ = (∑ k ∈ _root_.Finset.Icc 1 ⌊t⌋₊, ‖_root_.LSeries.term a (sigma : ℂ) k‖) * t ^ sigma :=
        (_root_.Finset.sum_mul ..).symm
    _ ≤ (∑' k : ℕ, ‖_root_.LSeries.term a (sigma : ℂ) k‖) * t ^ sigma := by
        have := hsummable.sum_le_tsum (_root_.Finset.Icc 1 ⌊t⌋₊) fun i _ ↦ _root_.norm_nonneg _
        have hrp : (0 : ℝ) ≤ t ^ sigma := by positivity
        exact _root_.mul_le_mul_of_nonneg_right this hrp
    _ ≤ B / (sigma - 1) * t ^ sigma := by
        have hrp : (0 : ℝ) ≤ t ^ sigma := by positivity
        exact _root_.mul_le_mul_of_nonneg_right hbound hrp
    _ = _root_.Real.exp 1 * B * (t * _root_.Real.log t) := by
        rw [hsig1, hpow]
        field_simp

/-! ### The Fourier weight -/





end TauCeti.LSeries

end
end
