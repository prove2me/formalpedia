-- Prove2me | solution 1 for TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:34:49.330886+00:00
-- url     : https://prove2.me/submissions/f444efe9-90f2-4a87-ac0c-1d8f8a8285ad

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.LSeries.Deriv
import Theorems.Thm_TauCeti_LSeries_integral_exp_mul_fourier_eq
import Theorems.Thm_TauCeti_LSeries_tsum_term_mul_fourier_eq_integral

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

/-- A Dirichlet series summable at `s` is continuous along the vertical line through `s`. -/
theorem continuous_LSeries_vertical (hs : LSeriesSummable a s) :
    Continuous fun t : ℝ ↦ LSeries a (s + t * I) := by
  refine (continuousOn_LSeries hs).comp_continuous (by fun_prop) fun t ↦ ?_
  simp



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
# Fourier identities for Wiener--Ikehara

The Fourier proof of Wiener--Ikehara starts by testing a Dirichlet series against an integrable
function on a vertical line. This file records the two exact identities used in that step. The
first exchanges the Dirichlet series with the integral. The second computes the contribution of
the simple pole at `s = 1`. Their combination expresses the difference as the integral of the
pole-subtracted remainder, a function agreeing with `LSeries a - A / (s - 1)` on the open
vertical line `Re s = sigma`; nothing about its boundary behaviour is asserted or used here.

## Main results

* `TauCeti.LSeries.tsum_term_mul_fourier_eq_integral` is the Fourier identity for a
  convergent Dirichlet series.
* `TauCeti.LSeries.integral_exp_mul_fourier_eq` computes the pole term.
* `TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral` combines the two when a named
  function agrees with the pole-subtracted remainder on the vertical line.

## Provenance

The proofs are adapted from `PrimeNumberTheoremAnd/Wiener.lean` in the Apache-2.0
`AxiomMath/PrimeNumberTheoremAnd` repository, revision
`2667e414c38e5a5dc9aa1946f16f13001e5cd3ed`. The source declarations are `first_fourier`,
`second_fourier`, and `limiting_fourier_aux`. The statements here use Mathlib's
`LSeriesSummable` directly, remove the source project's local `nterm` wrapper, and rely on
Mathlib's APIs together with the local vertical-line continuity theorem
`TauCeti.LSeries.continuous_LSeries_vertical`.

## References

* J. Korevaar, *Tauberian Theory: A Century of Developments*, Chapter III.
-/

 section

namespace TauCeti.LSeries
end TauCeti.LSeries
section TauCeti.LSeries
open TauCeti TauCeti.LSeries

open Complex Filter FourierTransform MeasureTheory Real Set
open scoped ComplexConjugate Real Topology

variable {a : ℕ → ℂ} {psi : ℝ → ℂ} {x sigma t : ℝ}















/-! ### The simple-pole term -/









/-! ### Subtracting the pole -/

/-- Subtracting the simple-pole Fourier identity from the Dirichlet-series identity leaves exactly
the integral of the pole-subtracted remainder `G`. Only the values of `G` on the vertical line
`Re s = sigma` enter, so no continuity or limiting behaviour of `G` on the boundary line is
assumed here. This is the form used before sending `sigma` to `1` in the Wiener--Ikehara
argument. -/
theorem solution {G : ℂ → ℂ} {A : ℂ}
    (hG : ∀ t : ℝ, G (sigma + t * _root_.Complex.I) = _root_.LSeries a (sigma + t * _root_.Complex.I) -
      A / (sigma + t * _root_.Complex.I - 1))
    (hpsi : _root_.MeasureTheory.Integrable psi) (hx : 0 < x)
    (hsigma : 1 < sigma) (hsigmaSum : _root_.LSeriesSummable a (sigma : ℂ)) :
    (∑' n : ℕ, _root_.LSeries.term a sigma n *
        _root_.FourierTransform.fourier psi (1 / (2 * π) * _root_.Real.log (n / x))) -
      A * (x ^ (1 - sigma) : ℝ) *
        ∫ u in _root_.Set.Ici (-_root_.Real.log x), _root_.Real.exp (-u * (sigma - 1)) *
          _root_.FourierTransform.fourier psi (u / (2 * π)) =
      ∫ t : ℝ, G (sigma + t * _root_.Complex.I) * psi t * x ^ (t * _root_.Complex.I) := by
  have hseries := _root_.TauCeti.LSeries.tsum_term_mul_fourier_eq_integral hpsi hx hsigmaSum
  have hpole := _root_.TauCeti.LSeries.integral_exp_mul_fourier_eq hpsi hx hsigma
  have hxpow : _root_.Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * _root_.Complex.I) :=
    continuous_const.cpow (continuous_ofReal.mul _root_.continuous_const) (by simp [hx])
  have hxnorm (t : ℝ) : ‖(x : ℂ) ^ (t * _root_.Complex.I)‖ = 1 := by
    rw [_root_.Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp
  have hdenom (t : ℝ) : (sigma : ℂ) + t * _root_.Complex.I - 1 ≠ 0 := by
    intro h
    have hre := _root_.congrArg _root_.Complex.re h
    simp at hre
    linarith
  -- The two integrands are bounded multiples of `psi`, so `Integrable psi` suffices.
  have hLbound (t : ℝ) : ‖_root_.LSeries a ((sigma : ℂ) + t * _root_.Complex.I) * (x : ℂ) ^ (t * _root_.Complex.I)‖ ≤
      ∑' n : ℕ, ‖_root_.LSeries.term a (sigma : ℂ) n‖ := by
    rw [_root_.norm_mul, hxnorm, _root_.mul_one]
    calc
      ‖_root_.LSeries a ((sigma : ℂ) + t * _root_.Complex.I)‖
          ≤ ∑' n : ℕ, ‖_root_.LSeries.term a ((sigma : ℂ) + t * _root_.Complex.I) n‖ :=
        _root_.norm_tsum_le_tsum_norm (summable_norm_iff.mpr (hsigmaSum.of_re_le_re (by simp)))
      _ = _ := by
        refine _root_.tsum_congr fun n ↦ ?_
        simp only [_root_.LSeries.norm_term_eq]
        simp
  have hpolebound (t : ℝ) :
      ‖1 / ((sigma : ℂ) + t * _root_.Complex.I - 1) * (x : ℂ) ^ (t * _root_.Complex.I)‖ ≤ (sigma - 1)⁻¹ := by
    rw [_root_.norm_mul, hxnorm, _root_.mul_one, _root_.norm_div, _root_.NormOneClass.norm_one, _root_.one_div]
    refine _root_.inv_anti₀ (by linarith) ?_
    calc
      sigma - 1 = ((sigma : ℂ) + t * _root_.Complex.I - 1).re := by simp
      _ ≤ _ := _root_.Complex.re_le_norm _
  have hseriesI : _root_.MeasureTheory.Integrable fun t : ℝ ↦
      _root_.LSeries a (sigma + t * _root_.Complex.I) * psi t * x ^ (t * _root_.Complex.I) := by
    exact (hpsi.bdd_mul (f := fun t : ℝ ↦ _root_.LSeries a ((sigma : ℂ) + t * _root_.Complex.I) * (x : ℂ) ^ (t * _root_.Complex.I))
      ((_root_.TauCeti.LSeries.continuous_LSeries_vertical hsigmaSum).mul hxpow).aestronglyMeasurable
      (.of_forall hLbound)).congr (.of_forall fun t ↦ by ring)
  have hpoleI : _root_.MeasureTheory.Integrable fun t : ℝ ↦
      A * (x ^ (1 - sigma) : ℝ) *
        ((x ^ (sigma - 1) : ℝ) * ((1 / (sigma + t * _root_.Complex.I - 1)) * psi t * x ^ (t * _root_.Complex.I))) := by
    have hbdd : _root_.MeasureTheory.Integrable fun t : ℝ ↦
        1 / ((sigma : ℂ) + t * _root_.Complex.I - 1) * (x : ℂ) ^ (t * _root_.Complex.I) * psi t := by
      refine hpsi.bdd_mul (f := fun t : ℝ ↦ 1 / ((sigma : ℂ) + t * _root_.Complex.I - 1) * (x : ℂ) ^ (t * _root_.Complex.I))
        ?_ (.of_forall hpolebound)
      exact ((continuous_const.div (by fun_prop) hdenom).mul hxpow).aestronglyMeasurable
    exact (hbdd.const_mul (A * (x ^ (1 - sigma) : ℝ) * (x ^ (sigma - 1) : ℝ))).congr
      (.of_forall fun t ↦ by ring)
  have hpoleConst :
      A * (x ^ (1 - sigma) : ℝ) *
          ((x ^ (sigma - 1) : ℝ) *
            ∫ t : ℝ, (1 / (sigma + t * _root_.Complex.I - 1)) * psi t * x ^ (t * _root_.Complex.I)) =
        ∫ t : ℝ, A * (x ^ (1 - sigma) : ℝ) *
          ((x ^ (sigma - 1) : ℝ) *
            ((1 / (sigma + t * _root_.Complex.I - 1)) * psi t * x ^ (t * _root_.Complex.I))) := by
    rw [_root_.MeasureTheory.integral_const_mul, _root_.MeasureTheory.integral_const_mul]
  rw [hseries, hpole, hpoleConst, ← _root_.MeasureTheory.integral_sub hseriesI hpoleI]
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [] with t
  rw [hG t, _root_.sub_mul]
  have hxpowOne :
      ((x ^ (1 - sigma) : ℝ) : ℂ) * ((x ^ (sigma - 1) : ℝ) : ℂ) = 1 := by
    norm_cast
    rw [← _root_.Real.rpow_add hx]
    simp
  calc
    _ = _root_.LSeries a (sigma + t * _root_.Complex.I) * psi t * x ^ (t * _root_.Complex.I) -
        A * (((x ^ (1 - sigma) : ℝ) : ℂ) * ((x ^ (sigma - 1) : ℝ) : ℂ)) *
          ((sigma + t * _root_.Complex.I - 1)⁻¹ * psi t * x ^ (t * _root_.Complex.I)) := by ring
    _ = _ := by rw [hxpowOne]; ring

end TauCeti.LSeries

end
end
