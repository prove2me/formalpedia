-- Prove2me | solution 1 for TauCeti.LSeries.tsum_term_mul_fourier_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:22:46.273654+00:00
-- url     : https://prove2.me/submissions/4308423e-3c0a-4be1-9450-5fd69a73cb6a

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_LSeries_WienerIkehara_Fourier
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.LSeries.Deriv

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





private lemma TauCeti.LSeries.fourierIntegrand_aemeasurable (hpsi : _root_.MeasureTheory.AEStronglyMeasurable psi)
    (x : ℝ) (n : ℕ) :
    _root_.AEMeasurable fun u : ℝ ↦
      (‖_root_.Real.fourierChar (-(u * (1 / (2 * π) * _root_.Real.log (n / x)))) • psi u‖ₑ : _root_.ENNReal) := by
  fun_prop

private lemma TauCeti.LSeries.two_pi_mul_neg_log_scale (y x : ℝ) (n : ℕ) :
    (2 : ℂ) * π * -(y * (1 / (2 * π) * _root_.Real.log (n / x))) =
      -(y * _root_.Real.log (n / x)) := by
  calc
    _ = -(y * (((2 : ℂ) * π) / (2 * π) * _root_.Real.log (n / x))) := by ring
    _ = _ := by rw [_root_.div_self (by norm_num), _root_.one_mul]

private lemma TauCeti.LSeries.term_mul_fourierChar (hx : 0 < x) (a : ℕ → ℂ) (n : ℕ) (y sigma : ℝ) :
    _root_.LSeries.term a sigma n *
        _root_.Real.fourierChar (-(y * (1 / (2 * π) * _root_.Real.log (n / x)))) • psi y =
      _root_.LSeries.term a (sigma + y * _root_.Complex.I) n • (psi y * x ^ (y * _root_.Complex.I)) := by
  by_cases hn : n = 0
  · simp [_root_.LSeries.term, hn]
  simp only [_root_.LSeries.term, hn, _root_.ite_false]
  calc
    _ = (a n * (cexp ((2 * π * -(y * (1 / (2 * π) * _root_.Real.log (n / x)))) * _root_.Complex.I) /
        ↑((n : ℝ) ^ sigma))) • psi y := by
      rw [_root_.Circle.smul_def, _root_.Real.fourierChar_apply, _root_.Complex.ofReal_cpow (by positivity)]
      simp only [_root_.one_div, _root_.mul_inv_rev, _root_.mul_neg, _root_.Complex.ofReal_neg, _root_.Complex.ofReal_mul, _root_.Complex.ofReal_ofNat,
        _root_.Complex.ofReal_inv, _root_.neg_mul, _root_.smul_eq_mul, _root_.Complex.ofReal_natCast]
      ring
    _ = (a n * (x ^ (y * _root_.Complex.I) / n ^ (sigma + y * _root_.Complex.I))) • psi y := by
      congr 2
      have hnpos : 0 < (n : ℝ) := by positivity
      have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      rw [_root_.Real.rpow_def_of_pos hnpos, _root_.Complex.cpow_def_of_ne_zero hx0,
        _root_.Complex.cpow_def_of_ne_zero hn0]
      push_cast
      rw [_root_.TauCeti.LSeries.two_pi_mul_neg_log_scale, _root_.Real.log_div hnpos.ne' hx.ne']
      push_cast
      rw [_root_.Complex.ofReal_log hx.le]
      conv_rhs => rw [← _root_.Complex.exp_sub]
      conv_lhs => rw [_root_.div_eq_mul_inv, ← _root_.Complex.exp_neg, ← _root_.Complex.exp_add]
      congr 1
      ring
    _ = _ := by simp; ring

private lemma TauCeti.LSeries.summable_enorm_term_ne_top (hsigma : _root_.LSeriesSummable a (sigma : ℂ)) :
    ∑' n, (‖_root_.LSeries.term a sigma n‖₊ : _root_.ENNReal) ≠ ⊤ := by
  simp_rw [_root_.ENNReal.tsum_coe_ne_top_iff_summable_coe, ← _root_.norm_toNNReal]
  norm_cast
  exact _root_.Summable.toNNReal (summable_norm_iff.mpr hsigma)

/-- Testing an absolutely convergent Dirichlet series against an integrable function on the
vertical line `Re s = sigma` can be done term by term. The Fourier transform is evaluated at the
logarithmic scale `(2π)⁻¹ log (n / x)` dictated by the factor `x ^ (it)`. -/
theorem solution (hpsi : _root_.MeasureTheory.Integrable psi) (hx : 0 < x)
    (hsigma : _root_.LSeriesSummable a (sigma : ℂ)) :
    ∑' n : ℕ, _root_.LSeries.term a sigma n *
        _root_.FourierTransform.fourier psi (1 / (2 * π) * _root_.Real.log (n / x)) =
      ∫ t : ℝ, _root_.LSeries a (sigma + t * _root_.Complex.I) * psi t * x ^ (t * _root_.Complex.I) := by
  calc
    _ = ∑' n : ℕ, _root_.LSeries.term a sigma n *
        ∫ u : ℝ, _root_.Real.fourierChar (-(u * (1 / (2 * π) * _root_.Real.log (n / x)))) • psi u := by
      simp only [_root_.Real.fourier_eq, _root_.one_div, _root_.mul_inv_rev, _root_.RCLike.inner_apply', _root_.conj_trivial]
    _ = ∑' n : ℕ, ∫ u : ℝ,
        _root_.LSeries.term a sigma n *
          _root_.Real.fourierChar (-(u * (1 / (2 * π) * _root_.Real.log (n / x)))) • psi u := by
      simp only [_root_.MeasureTheory.integral_const_mul]
    _ = ∫ u : ℝ, ∑' n : ℕ,
        _root_.LSeries.term a sigma n *
          _root_.Real.fourierChar (-(u * (1 / (2 * π) * _root_.Real.log (n / x)))) • psi u := by
      refine (_root_.MeasureTheory.integral_tsum (fun _ ↦ ?_) ?_).symm
      · apply _root_.AEMeasurable.aestronglyMeasurable
        apply _root_.AEMeasurable.mul
        · exact _root_.aemeasurable_const
        · exact (by fun_prop : Measurable fun u : ℝ ↦
            fourierChar (-(u * (1 / (2 * π) * Real.log (_ / x))))).aemeasurable.smul
              hpsi.aemeasurable
      · simp only [_root_.enorm_mul]
        simp_rw [_root_.MeasureTheory.lintegral_const_mul'' _ (_root_.TauCeti.LSeries.fourierIntegrand_aemeasurable hpsi.aestronglyMeasurable
          x _)]
        calc
          _ = (∑' n : ℕ, ‖_root_.LSeries.term a sigma n‖ₑ) *
              ∫⁻ u : ℝ, ‖psi u‖ₑ := by
            have hc (z : _root_.Circle) : ‖(z : ℂ)‖₊ = 1 := by
              apply _root_.NNReal.coe_injective
              exact _root_.Circle.norm_coe z
            simp [_root_.ENNReal.tsum_mul_right, _root_.enorm_eq_nnnorm, _root_.Circle.smul_def, hc]
          _ ≠ ⊤ := _root_.ENNReal.mul_ne_top (_root_.TauCeti.LSeries.summable_enorm_term_ne_top hsigma)
            (_root_.ne_top_of_lt hpsi.2)
    _ = _ := by
      congr 1
      ext y
      simp_rw [_root_.mul_assoc (_root_.LSeries a _), ← _root_.smul_eq_mul (a := _root_.LSeries a _), _root_.LSeries]
      rw [← _root_.Summable.tsum_smul_const]
      · simp_rw [_root_.TauCeti.LSeries.term_mul_fourierChar hx]
      · exact hsigma.of_re_le_re (by simp)

/-! ### The simple-pole term -/









/-! ### Subtracting the pole -/



end TauCeti.LSeries

end
end
