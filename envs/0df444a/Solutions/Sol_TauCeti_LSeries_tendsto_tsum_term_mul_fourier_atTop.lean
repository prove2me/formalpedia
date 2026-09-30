-- Prove2me | solution 1 for TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:56:26.488472+00:00
-- url     : https://prove2.me/submissions/429f7d55-e33d-430f-9121-b0e2017b0a64

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.NumberTheory.LSeries.Deriv
import Theorems.Thm_TauCeti_LSeries_tsum_term_mul_fourier_sub_pole_eq_integral_boundary
import Theorems.Thm_TauCeti_tendsto_integral_mul_cpow_mul_I_atTop

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The smoothed asymptotic behind Wiener--Ikehara

`TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral_boundary_of_contDiff` writes the
difference between a Fourier-weighted Dirichlet series and its pole contribution as an integral
along the line `Re s = 1`, for every scale `x > 0`. That integral carries the oscillating factor
`x ^ (it)`, so the Riemann--Lebesgue lemma makes it vanish as `x → ∞`. This file records the
resulting asymptotic, and then evaluates the pole contribution in the limit.

The pole contribution is `A * ∫ u in Ici (-log x), 𝓕 psi (u / 2π)`. As `x → ∞` the cutoff
`-log x` runs off to `-∞`, so the integral fills up the whole line, where Fourier inversion
evaluates it as `2π * psi 0`. The Fourier-weighted series therefore has the honest limit
`2π * A * psi 0`; the constant `2π` is the Jacobian of the scaling `u ↦ u / 2π` fixed by the
`x ^ (it)` parameterization.

Only the pole-subtracted remainder `G` is assumed continuous on the closed half-plane `Re s ≥ 1`.
Nothing is assumed about `LSeries a` there, where it is a total function with junk values.

## Main results

* `TauCeti.LSeries.tendsto_tsum_term_mul_fourier_sub_pole_atTop`: the Fourier-weighted Dirichlet
  series and its pole contribution differ by `o(1)` as the scale `x` tends to infinity.
* `TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop`: the Fourier-weighted Dirichlet series
  itself tends to `2π * A * psi 0`.

Both are stated for an integrable, compactly supported test function, with the analytic
hypotheses that the two limit arguments actually consume: half-line integrability of `𝓕 psi` for
the first, and integrability of `𝓕 psi` together with continuity of `psi` at `0` for the Fourier
inversion in the second. The hypotheses that vary with the scale `x` are asked for only
eventually as `x → ∞`, which is all an `atTop` limit consumes. The suffixed `..._of_contDiff`
forms specialize both to a smooth test function, for which all of those are automatic.

## Provenance

The statement obtained by letting `x → ∞` in the boundary Fourier identity follows `limiting_cor`
in `PrimeNumberTheoremAnd/Wiener.lean` of the Apache-2.0 `AxiomMath/PrimeNumberTheoremAnd`
repository, revision `2667e414c38e5a5dc9aa1946f16f13001e5cd3ed`, the same source as the sibling
files `TauCeti.NumberTheory.LSeries.WienerIkehara.Fourier` and
`TauCeti.NumberTheory.LSeries.WienerIkehara.Limit`. The evaluation of the limiting pole
contribution by Fourier inversion is not in that source, which keeps the truncated integral.

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

variable {a : ℕ → ℂ} {psi : ℝ → ℂ} {G : ℂ → ℂ} {A : ℂ}

/-- As the scale `x` tends to infinity, the Fourier-weighted Dirichlet series on the line
`Re s = 1` and the contribution of the pole term `A / (s - 1)` at `s = 1` differ by `o(1)`.

This is the Riemann--Lebesgue lemma applied to the boundary identity
`tsum_term_mul_fourier_sub_pole_eq_integral_boundary`, whose right-hand side is an integral
against the oscillating factor `x ^ (it)`. The test function is only required to be integrable
and compactly supported, with its Fourier transform integrable on the half-line `Ici (-log x)`
for all large `x`, which is where the limit reads that identity off. -/
theorem TauCeti.LSeries.tendsto_tsum_term_mul_fourier_sub_pole_atTop
    (hG : _root_.ContinuousOn G {z : ℂ | 1 ≤ z.re})
    (hG' : ∀ z : ℂ, 1 < z.re → G z = _root_.LSeries a z - A / (z - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → _root_.LSeriesSummable a sigma)
    (hpsi : _root_.MeasureTheory.Integrable psi) (hsupp : _root_.HasCompactSupport psi)
    (hFint : ∀ᶠ x : ℝ in _root_.Filter.atTop,
      _root_.MeasureTheory.IntegrableOn (fun u : ℝ ↦ 𝓕 psi (u / (2 * π))) (_root_.Set.Ici (-_root_.Real.log x)))
    (hFsum : ∀ᶠ x : ℝ in _root_.Filter.atTop, _root_.LSeriesSummable
      (fun n : ℕ ↦ a n * 𝓕 psi (1 / (2 * π) * _root_.Real.log (n / x))) 1) :
    _root_.Filter.Tendsto (fun x : ℝ ↦
        (∑' n : ℕ, _root_.LSeries.term a 1 n * 𝓕 psi (1 / (2 * π) * _root_.Real.log (n / x))) -
          A * ∫ u in _root_.Set.Ici (-_root_.Real.log x), 𝓕 psi (u / (2 * π))) _root_.Filter.atTop (𝓝 0) := by
  refine _root_.Filter.Tendsto.congr' ?_
    (_root_.TauCeti.tendsto_integral_mul_cpow_mul_I_atTop fun t : ℝ ↦ G (1 + t * _root_.Complex.I) * psi t)
  filter_upwards [_root_.Filter.eventually_gt_atTop 0, hFint, hFsum] with x hx hxint hxsum
  exact (_root_.TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral_boundary hx hG hG' hsum hpsi hsupp
    hxint hxsum).symm



/-- **The smoothed Wiener--Ikehara asymptotic.** The Fourier-weighted Dirichlet series on the line
`Re s = 1` tends to `2π * A * psi 0`, where `A` is the coefficient of the pole term `A / (s - 1)`
that the continuous boundary remainder `G` subtracts off. The hypotheses allow `A = 0`, in which
case no pole is asserted and the limit is `0`.

The factor `2π` is the Jacobian of the scaling `u ↦ u / 2π` that the parameterization
`s = 1 + it` forces on the Fourier variable; by Fourier inversion the limiting pole contribution
is `A * ∫ u : ℝ, 𝓕 psi (u / 2π) = 2π * A * psi 0`. The inversion step is what asks for the
integrability of `𝓕 psi` and the continuity of `psi` at the single point `0`. -/
theorem solution
    (hG : _root_.ContinuousOn G {z : ℂ | 1 ≤ z.re})
    (hG' : ∀ z : ℂ, 1 < z.re → G z = _root_.LSeries a z - A / (z - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → _root_.LSeriesSummable a sigma)
    (hpsi : _root_.MeasureTheory.Integrable psi) (hsupp : _root_.HasCompactSupport psi) (hF : _root_.MeasureTheory.Integrable (𝓕 psi))
    (hpsi0 : _root_.ContinuousAt psi 0)
    (hFsum : ∀ᶠ x : ℝ in _root_.Filter.atTop, _root_.LSeriesSummable
      (fun n : ℕ ↦ a n * 𝓕 psi (1 / (2 * π) * _root_.Real.log (n / x))) 1) :
    _root_.Filter.Tendsto (fun x : ℝ ↦
        ∑' n : ℕ, _root_.LSeries.term a 1 n * 𝓕 psi (1 / (2 * π) * _root_.Real.log (n / x)))
      _root_.Filter.atTop (𝓝 (2 * (π : ℂ) * A * psi 0)) := by
  have hint : _root_.MeasureTheory.Integrable fun u : ℝ ↦ 𝓕 psi (u / (2 * π)) := hF.comp_div (by positivity)
  have hIci : _root_.Filter.Tendsto (fun x : ℝ ↦ ∫ u in _root_.Set.Ici (-_root_.Real.log x), 𝓕 psi (u / (2 * π))) _root_.Filter.atTop
      (𝓝 (∫ u : ℝ, 𝓕 psi (u / (2 * π)))) :=
    _root_.MeasureTheory.AECover.integral_tendsto_of_countably_generated
      (_root_.MeasureTheory.aecover_Ici (tendsto_neg_atTop_atBot.comp _root_.Real.tendsto_log_atTop)) hint
  have htotal : (∫ v : ℝ, 𝓕 psi v) = psi 0 := by
    have hinv : 𝓕⁻ (𝓕 psi) 0 = psi 0 := hpsi.fourierInv_fourier_eq hF hpsi0
    rw [_root_.Real.fourierInv_eq] at hinv
    simpa using hinv
  have hvalue : (∫ u : ℝ, 𝓕 psi (u / (2 * π))) = 2 * (π : ℂ) * psi 0 := by
    rw [_root_.MeasureTheory.Measure.integral_comp_div, htotal, _root_.abs_of_pos (by positivity : (0 : ℝ) < 2 * π),
      _root_.Complex.real_smul]
    push_cast
    ring
  have hconst : 2 * (π : ℂ) * A * psi 0 = A * ∫ u : ℝ, 𝓕 psi (u / (2 * π)) := by
    rw [hvalue]
    ring
  have hpole : _root_.Filter.Tendsto (fun x : ℝ ↦ A * ∫ u in _root_.Set.Ici (-_root_.Real.log x), 𝓕 psi (u / (2 * π))) _root_.Filter.atTop
      (𝓝 (2 * (π : ℂ) * A * psi 0)) := by
    rw [hconst]
    exact hIci.const_mul A
  simpa using (_root_.TauCeti.LSeries.tendsto_tsum_term_mul_fourier_sub_pole_atTop hG hG' hsum hpsi hsupp
    (.of_forall fun _ ↦ hint.integrableOn) hFsum).add hpole



end TauCeti.LSeries

end
end
