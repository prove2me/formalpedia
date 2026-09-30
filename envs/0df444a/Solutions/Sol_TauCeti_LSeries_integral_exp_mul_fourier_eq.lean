-- Prove2me | solution 1 for TauCeti.LSeries.integral_exp_mul_fourier_eq
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:22:44.537761+00:00
-- url     : https://prove2.me/submissions/2375041a-1a56-46b4-8d98-567f2db9cf4a

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
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















/-! ### The simple-pole term -/

private lemma TauCeti.LSeries.exp_mul_integrableOn_Ici (hsigma : 1 < sigma) (x : ℝ) :
    _root_.MeasureTheory.IntegrableOn (fun u : ℝ ↦ cexp (-(u * (sigma - 1)))) (_root_.Set.Ici (-_root_.Real.log x)) := by
  have harg (u : ℝ) : (1 - (sigma : ℂ)) * u = -(u * (sigma - 1)) := by ring
  rw [_root_.integrableOn_Ici_iff_integrableOn_Ioi]
  exact (_root_.integrableOn_exp_mul_complex_Ioi (a := 1 - (sigma : ℂ)) (by simp; linarith)
    _).congr_fun (fun u _ ↦ by simp only [harg]) _root_.measurableSet_Ioi

private lemma TauCeti.LSeries.poleFubiniIntegrable (hpsi : _root_.MeasureTheory.Integrable psi) (hsigma : 1 < sigma) (x : ℝ) :
    _root_.MeasureTheory.Integrable (_root_.Function.uncurry fun (u v : ℝ) ↦
        (_root_.Real.exp (-u * (sigma - 1)) : ℂ) *
          ((_root_.Real.fourierChar (-(v * (u / (2 * π)))) : ℂ) * psi v))
      ((volume.restrict (_root_.Set.Ici (-_root_.Real.log x))).prod _root_.MeasureTheory.MeasureSpace.volume) := by
  constructor
  · exact _root_.MeasureTheory.AEStronglyMeasurable.mul (_root_.Measurable.aestronglyMeasurable (by fun_prop))
      (_root_.MeasureTheory.AEStronglyMeasurable.mul (_root_.Measurable.aestronglyMeasurable (by fun_prop))
        hpsi.aestronglyMeasurable.comp_snd)
  · let f₁ : ℝ → _root_.ENNReal := fun u ↦ ‖cexp (-(u * (sigma - 1)))‖ₑ
    let f₂ : ℝ → _root_.ENNReal := fun v ↦ ‖psi v‖ₑ
    suffices ∫⁻ p : ℝ × ℝ, f₁ p.1 * f₂ p.2
        ∂((volume.restrict (_root_.Set.Ici (-_root_.Real.log x))).prod _root_.MeasureTheory.MeasureSpace.volume) < ⊤ by
      have hc (z : _root_.Circle) : ‖(z : ℂ)‖₊ = 1 := by
        apply _root_.NNReal.coe_injective
        exact _root_.Circle.norm_coe z
      simpa [_root_.MeasureTheory.hasFiniteIntegral_iff_enorm, _root_.enorm_eq_nnnorm, _root_.Function.uncurry,
        _root_.Complex.norm_exp, hc]
    refine (_root_.MeasureTheory.lintegral_prod_mul ?_ ?_).trans_lt ?_ <;> try fun_prop
    exact _root_.ENNReal.mul_lt_top (_root_.TauCeti.LSeries.exp_mul_integrableOn_Ici hsigma x).2 hpsi.2

private lemma TauCeti.LSeries.polePrimitive_at_lowerEndpoint (hx : 0 < x) (t sigma : ℝ) :
    -cexp ((1 - sigma - t * _root_.Complex.I) * ((-_root_.Real.log x : ℝ) : ℂ)) / (1 - sigma - t * _root_.Complex.I) =
      (x ^ (sigma - 1) : ℝ) * (1 / (sigma + t * _root_.Complex.I - 1)) * x ^ (t * _root_.Complex.I) := by
  have harg : (1 - (sigma : ℂ) - t * _root_.Complex.I) * ((-_root_.Real.log x : ℝ) : ℂ) =
      _root_.Real.log x * ((sigma - 1) + t * _root_.Complex.I) := by
    push_cast
    ring
  have hflip : (1 - (sigma : ℂ) - t * _root_.Complex.I) = -((sigma : ℂ) + t * _root_.Complex.I - 1) := by ring
  calc
    _ = cexp (_root_.Real.log x * ((sigma - 1) + t * _root_.Complex.I)) * (sigma + t * _root_.Complex.I - 1)⁻¹ := by
      rw [harg, hflip, _root_.div_neg, _root_.neg_div, _root_.neg_neg, _root_.div_eq_mul_inv]
    _ = x ^ ((sigma - 1) + t * _root_.Complex.I) * (sigma + t * _root_.Complex.I - 1)⁻¹ := by
      rw [_root_.Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), _root_.Complex.ofReal_log hx.le]
    _ = x ^ ((sigma : ℂ) - 1) * x ^ (t * _root_.Complex.I) * (sigma + t * _root_.Complex.I - 1)⁻¹ := by
      rw [_root_.Complex.cpow_add _ _ (ofReal_ne_zero.mpr hx.ne')]
    _ = _ := by rw [_root_.Complex.ofReal_cpow hx.le]; push_cast; ring

/-- The one-sided Laplace transform `∫ u in Ici (-log x), exp (-u * (sigma - 1)) * 𝓕 psi (u / 2π)`
equals `x ^ (sigma - 1)` times the Fourier integral of the simple pole `1 / (s - 1)` on the line
`Re s = sigma`. This is the pole term subtracted in the Wiener--Ikehara boundary argument, and the
factor `x ^ (sigma - 1)` is the normalization that makes it match the Dirichlet-series identity. -/
theorem solution (hpsi : _root_.MeasureTheory.Integrable psi) (hx : 0 < x) (hsigma : 1 < sigma) :
    ∫ u in _root_.Set.Ici (-_root_.Real.log x), _root_.Real.exp (-u * (sigma - 1)) *
        _root_.FourierTransform.fourier psi (u / (2 * π)) =
      (x ^ (sigma - 1) : ℝ) *
        ∫ t : ℝ, (1 / (sigma + t * _root_.Complex.I - 1)) * psi t * x ^ (t * _root_.Complex.I) := by
  conv in (_root_.Real.exp _ : ℂ) * _ =>
    rw [_root_.Real.fourier_real_eq, ← _root_.smul_eq_mul, ← _root_.MeasureTheory.integral_smul]
  rw [_root_.MeasureTheory.integral_integral_swap]
  swap
  · exact _root_.TauCeti.LSeries.poleFubiniIntegrable hpsi hsigma x
  rw [← _root_.MeasureTheory.integral_const_mul]
  congr 1
  ext t
  have hpull (b c d : ℂ) : b * (c * psi t * d) = b * c * d * psi t := by ring
  rw [hpull]
  conv =>
    lhs
    enter [2]
    ext u
    rw [_root_.Circle.smul_def, _root_.Real.fourierChar_apply]
  push_cast
  simp_rw [_root_.smul_eq_mul]
  simp_rw [← _root_.mul_assoc]
  simp_rw [← _root_.Complex.exp_add]
  rw [_root_.MeasureTheory.integral_mul_const]
  congr 1
  have hexp (u : ℝ) :
      -u * (sigma - 1) + 2 * π * -(t * (u / (2 * π))) * _root_.Complex.I =
        (1 - sigma - t * _root_.Complex.I) * u := by
    calc
      _ = -u * (sigma - 1) + (2 * π) / (2 * π) * -(t * u) * _root_.Complex.I := by ring
      _ = -u * (sigma - 1) + 1 * -(t * u) * _root_.Complex.I := by rw [_root_.div_self (by norm_num)]
      _ = _ := by ring
  simp_rw [hexp]
  rw [_root_.MeasureTheory.integral_Ici_eq_integral_Ioi,
    _root_.integral_exp_mul_complex_Ioi (by simp; linarith) (-_root_.Real.log x)]
  exact _root_.TauCeti.LSeries.polePrimitive_at_lowerEndpoint hx t sigma

/-! ### Subtracting the pole -/



end TauCeti.LSeries

end
end
