-- Prove2me | solution 1 for TauCeti.LSeries.tendsto_tsum_term_mul_fourier
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:17:21.465984+00:00
-- url     : https://prove2.me/submissions/e2c64666-7825-46de-af5f-427529306c57

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.LSeries.Deriv

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Continuity of an L-series on a closed half-plane of summability

If a Dirichlet series is summable at `s`, then at every point `z` with `s.re ≤ z.re` its terms
have norms at most those of the terms at `s`, so the series converges uniformly on the closed
half-plane `{z | s.re ≤ z.re}` and `LSeries a` is continuous there. On the vertical line
`s + ℝ * I` through `s` the norms even agree exactly, and continuity along that line is a special
case of the half-plane statement.

Mathlib's `LSeries_differentiableOn` gives more, but only *strictly* inside the half-plane of
absolute convergence: it needs `abscissaOfAbsConv a < s.re`, whereas `LSeriesSummable a s` only
gives `abscissaOfAbsConv a ≤ s.re`. The line through a point of summability may therefore be the
boundary line of that half-plane, which is exactly the situation in the Wiener--Ikehara argument.

## Main results

* `TauCeti.LSeries.continuousOn_LSeries`: `LSeries a` is continuous on the closed half-plane
  `{z | s.re ≤ z.re}` whenever `LSeriesSummable a s`.
* `TauCeti.LSeries.continuous_LSeries_vertical`: `fun t : ℝ ↦ LSeries a (s + t * I)` is continuous
  whenever `LSeriesSummable a s`.
* `TauCeti.LSeries.tendsto_LSeries_nhdsGT`: the real one-sided limit of `LSeries a` at a real
  point of summability is the value there.
-/

 section

namespace TauCeti.LSeries

open Complex Filter Topology

variable {a : ℕ → ℂ} {s : ℂ}

/-- A Dirichlet series summable at `s` converges uniformly on the closed half-plane
`{z | s.re ≤ z.re}`, hence is continuous there.

Mathlib's `LSeries_differentiableOn` gives more on the *open* half-plane cut out by the abscissa
of absolute convergence, but says nothing on its boundary line, which is where the
Wiener--Ikehara argument works. -/
theorem continuousOn_LSeries (hs : LSeriesSummable a s) :
    ContinuousOn (LSeries a) {z : ℂ | s.re ≤ z.re} :=
  continuousOn_tsum
    (fun n z _ ↦ (_root_.LSeries.hasDerivAt_term a n z).continuousAt.continuousWithinAt)
    (summable_norm_iff.mpr hs) (fun n _ hz ↦ _root_.LSeries.norm_term_le_of_re_le_re a hz n)



/-- Approaching a real point of summability from the right along the real axis, the values of a
Dirichlet series converge to its value there. -/
theorem tendsto_LSeries_nhdsGT {σ : ℝ} (hs : LSeriesSummable a σ) :
    Tendsto (fun τ : ℝ ↦ LSeries a τ) (𝓝[>] σ) (𝓝 (LSeries a σ)) := by
  refine Filter.Tendsto.comp (continuousOn_LSeries hs (σ : ℂ) (by simp)) ?_
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((Complex.continuous_ofReal.tendsto σ).mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  simpa using hτ.le

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
# The limiting Fourier identity for Wiener--Ikehara

`TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral` tests a Dirichlet series against an
integrable function on a vertical line `Re s = sigma` strictly inside the half-plane of
convergence. This file lets `sigma` decrease to `1` and records the resulting identity on the
boundary line itself.

Each of the three terms of that identity has its own limit argument, and each is stated separately
so that a later step can reuse it: the Dirichlet series converges by the uniform convergence of a
summable Dirichlet series on a closed half-plane, while the two integrals converge by dominated
convergence, the pole term because the exponential damping `exp (-u (sigma - 1))` is bounded on
the half-line of integration, and the vertical integral because a test function with compact
support confines the integrand to a compact box on which `G` is continuous.

Only the pole-subtracted remainder `G` is assumed continuous on the closed half-plane
`Re s ≥ 1`; nothing is assumed about `LSeries a` there, where it is a total function with junk
values.

## Main results

* `TauCeti.LSeries.tendsto_tsum_term_mul_fourier` and
  `TauCeti.LSeries.tendsto_integral_vertical` are two of the three one-sided limits; the third,
  for the pole term, is the general `TauCeti.tendsto_integral_exp_mul`.
* `TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral_boundary` is the identity they
  combine into, and
  `TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral_boundary_of_contDiff` is its form
  for a smooth test function, where the half-line integrability hypothesis is automatic by
  `TauCeti.integrable_fourier_of_contDiff_of_hasCompactSupport`.

## Provenance

The decomposition into three separate one-sided limits, and the shape of the identity they
combine into, follow `limiting_fourier_lim1`, `limiting_fourier_lim2`, `limiting_fourier_lim3`
and `limiting_fourier` in `PrimeNumberTheoremAnd/Wiener.lean` of the Apache-2.0
`AxiomMath/PrimeNumberTheoremAnd` repository, revision
`2667e414c38e5a5dc9aa1946f16f13001e5cd3ed`, the same source as the sibling file
`TauCeti.NumberTheory.LSeries.WienerIkehara.Fourier`. The proofs here are written against
Mathlib's uniform- and dominated-convergence lemmas, and the hypotheses differ: the Chebyshev-type
bound of the source is replaced by the summability of the Fourier-weighted series at `s = 1`,
which is what the limit actually consumes.

## References

* J. Korevaar, *Tauberian Theory: A Century of Developments*, Chapter III.
-/

 section

namespace TauCeti.LSeries
end TauCeti.LSeries
section TauCeti.LSeries
open TauCeti TauCeti.LSeries

open Complex Filter FourierTransform MeasureTheory Real Set
open scoped ContDiff Topology

variable {a : ℕ → ℂ} {psi : ℝ → ℂ} {G : ℂ → ℂ} {A : ℂ} {x : ℝ}

/-! ### The Dirichlet series -/

/-- As `sigma` decreases to `1`, the Fourier-weighted Dirichlet series converges to its value on
the boundary line, provided the weighted series is summable there. -/
theorem solution (hFsum : _root_.LSeriesSummable
    (fun n : ℕ ↦ a n * 𝓕 psi (1 / (2 * π) * _root_.Real.log (n / x))) 1) :
    _root_.Filter.Tendsto (fun sigma : ℝ ↦ ∑' n : ℕ,
        _root_.LSeries.term a sigma n * 𝓕 psi (1 / (2 * π) * _root_.Real.log (n / x))) (𝓝[>] 1)
      (𝓝 (∑' n : ℕ, _root_.LSeries.term a 1 n * 𝓕 psi (1 / (2 * π) * _root_.Real.log (n / x)))) := by
  have hterm (s : ℂ) (n : ℕ) :
      _root_.LSeries.term a s n * 𝓕 psi (1 / (2 * π) * _root_.Real.log (n / x)) =
        _root_.LSeries.term
          (fun n : ℕ ↦ a n * 𝓕 psi (1 / (2 * π) * _root_.Real.log (n / x))) s n := by
    by_cases hn : n = 0
    · simp [_root_.LSeries.term, hn]
    · simp only [_root_.LSeries.term, hn, _root_.ite_false]
      ring
  have h := _root_.TauCeti.LSeries.tendsto_LSeries_nhdsGT
    (a := fun n : ℕ ↦ a n * 𝓕 psi (1 / (2 * π) * _root_.Real.log (n / x))) (σ := 1)
    (by simpa using hFsum)
  rw [_root_.Complex.ofReal_one] at h
  simp only [hterm]
  exact h

/-! ### The integral along the vertical line -/



/-! ### The identity on the boundary line -/





end TauCeti.LSeries

end
end
