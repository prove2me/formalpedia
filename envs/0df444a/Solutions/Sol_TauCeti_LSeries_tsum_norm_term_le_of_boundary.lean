-- Prove2me | solution 1 for TauCeti.LSeries.tsum_norm_term_le_of_boundary
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:17:16.035188+00:00
-- url     : https://prove2.me/submissions/4675ad44-d4bd-4ba4-b2c7-4e7ef79e28f2

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

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Terms of a Dirichlet series with nonnegative coefficients at a real point

At a real point `sigma`, the terms of a Dirichlet series with nonnegative coefficients are
themselves nonnegative reals. Each term therefore equals its own norm, plain summability at `sigma`
is already absolute summability, and the value of the series is the sum of the norms of its terms.
These are the facts that turn a bound on the value `LSeries a sigma` into a bound on
`∑' n, ‖LSeries.term a sigma n‖`, which is the shape a comparison or truncation argument needs.

Mathlib's `Mathlib/NumberTheory/LSeries/Positivity.lean` records the positivity of the *values* of
such a series; the statements here are about its individual terms.

## Main declarations

* `TauCeti.LSeries.term_eq_ofReal_norm_of_nonneg`: a nonnegative coefficient makes the term at a
  real point equal to its own norm.
* `TauCeti.LSeries.summable_norm_term_of_nonneg`: for nonnegative coefficients, summability at a
  real point is absolute summability.
* `TauCeti.LSeries.LSeries_eq_ofReal_tsum_norm_of_nonneg`: for nonnegative coefficients, the value
  at a real point is the sum of the norms of the terms.
-/

 section

namespace TauCeti.LSeries

open scoped ComplexOrder

variable {a : ℕ → ℂ}

/-- At a real point, a nonnegative Dirichlet coefficient gives a term equal to its own norm. -/
theorem term_eq_ofReal_norm_of_nonneg {n : ℕ} (ha : 0 ≤ a n) (sigma : ℝ) :
    _root_.LSeries.term a (sigma : ℂ) n = (‖_root_.LSeries.term a (sigma : ℂ) n‖ : ℂ) :=
  Complex.eq_coe_norm_of_nonneg (_root_.LSeries.term_nonneg ha sigma)

/-- For nonnegative coefficients, summability at a real point is absolute summability. -/
theorem summable_norm_term_of_nonneg (ha : 0 ≤ a) {sigma : ℝ}
    (h : LSeriesSummable a sigma) :
    Summable fun n : ℕ ↦ ‖_root_.LSeries.term a (sigma : ℂ) n‖ := by
  rw [← Complex.summable_ofReal]
  exact h.congr fun n ↦ term_eq_ofReal_norm_of_nonneg (ha n) sigma

/-- For nonnegative coefficients, the value of the Dirichlet series at a real point is the sum of
the norms of its terms. -/
theorem LSeries_eq_ofReal_tsum_norm_of_nonneg (ha : 0 ≤ a) (sigma : ℝ) :
    LSeries a (sigma : ℂ) = ((∑' n : ℕ, ‖_root_.LSeries.term a (sigma : ℂ) n‖ : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  exact tsum_congr fun n ↦ term_eq_ofReal_norm_of_nonneg (ha n) sigma

end TauCeti.LSeries

end
end

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

/-- For nonnegative coefficients, a boundary remainder `G` continuous on the real segment `[1, 2]`
bounds the Dirichlet series on `(1, 2]` by `B / (sigma - 1)`: the remainder is bounded on the
compact segment, and the pole term contributes `‖A‖ / (sigma - 1)`.

No analytic continuation is used, only the values of `G` on that segment and the identity
`G = LSeries a - A / (s - 1)` on its interior. -/
theorem solution (ha : 0 ≤ a)
    (hG : _root_.ContinuousOn (fun sigma : ℝ ↦ G (sigma : ℂ)) (_root_.Set.Icc 1 2))
    (hG' : ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 →
      G (sigma : ℂ) = _root_.LSeries a (sigma : ℂ) - A / ((sigma : ℂ) - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 → _root_.LSeriesSummable a (sigma : ℂ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 →
      _root_.Summable (fun n : ℕ ↦ ‖_root_.LSeries.term a (sigma : ℂ) n‖) ∧
        ∑' n : ℕ, ‖_root_.LSeries.term a (sigma : ℂ) n‖ ≤ B / (sigma - 1) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hG
  have hM0 : 0 ≤ M := _root_.le_trans (_root_.norm_nonneg _) (hM 1 ⟨_root_.le_rfl, _root_.one_le_two⟩)
  refine ⟨M + ‖A‖, by positivity, fun sigma h1 h2 ↦
    ⟨_root_.TauCeti.LSeries.summable_norm_term_of_nonneg ha (hsum sigma h1 h2), ?_⟩⟩
  have hsub : (sigma : ℂ) - 1 = ((sigma - 1 : ℝ) : ℂ) := by push_cast; ring
  have hnorm : ‖A / ((sigma : ℂ) - 1)‖ = ‖A‖ / (sigma - 1) := by
    rw [hsub, _root_.norm_div, _root_.Complex.norm_real, _root_.Real.norm_of_nonneg (by linarith)]
  have hnn : (0 : ℝ) ≤ ∑' n : ℕ, ‖_root_.LSeries.term a (sigma : ℂ) n‖ :=
    _root_.tsum_nonneg fun _ ↦ _root_.norm_nonneg _
  have hS : ((∑' n : ℕ, ‖_root_.LSeries.term a (sigma : ℂ) n‖ : ℝ) : ℂ) =
      G (sigma : ℂ) + A / ((sigma : ℂ) - 1) := by
    rw [← _root_.TauCeti.LSeries.LSeries_eq_ofReal_tsum_norm_of_nonneg ha sigma, hG' sigma h1 h2]
    ring
  have hMdiv : M ≤ M / (sigma - 1) := by
    rw [_root_.le_div_iff₀ (by linarith : (0 : ℝ) < sigma - 1)]
    nlinarith
  have hkey : ∑' n : ℕ, ‖_root_.LSeries.term a (sigma : ℂ) n‖ ≤ M + ‖A‖ / (sigma - 1) := by
    calc ∑' n : ℕ, ‖_root_.LSeries.term a (sigma : ℂ) n‖
        = ‖((∑' n : ℕ, ‖_root_.LSeries.term a (sigma : ℂ) n‖ : ℝ) : ℂ)‖ := by
          rw [_root_.Complex.norm_real, _root_.Real.norm_of_nonneg hnn]
      _ ≤ ‖G (sigma : ℂ)‖ + ‖A / ((sigma : ℂ) - 1)‖ := by rw [hS]; exact _root_.norm_add_le _ _
      _ ≤ M + ‖A‖ / (sigma - 1) := by
          rw [hnorm]
          gcongr
          exact hM sigma ⟨h1.le, h2⟩
  rw [_root_.add_div]
  linarith

/-! ### The partial-sum bound -/



/-! ### The Fourier weight -/





end TauCeti.LSeries

end
end
