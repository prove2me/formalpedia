-- Prove2me | solution 1 for TauCeti.summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:15:56.842565+00:00
-- url     : https://prove2.me/submissions/ba349b22-e87e-4c62-9b83-1d62484f5c5c

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Regroup
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Topology.Algebra.InfiniteSum.Real

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Regrouping an ideal-indexed Dirichlet series by absolute norm

An `TauCeti.IdealArithmeticFunction K` has two Dirichlet series attached to it: the series indexed
by the nonzero integral ideals of `𝓞 K`, whose terms are `TauCeti.idealTerm`, and the Mathlib
`LSeries` of the regrouped coefficients `TauCeti.normCoeff`. This file proves that the second is
obtained from the first by summing over the finite absolute-norm fibres, so that absolute
convergence of the ideal-indexed series transfers to the `LSeries` together with the value of the
sum.

## Main definitions

* `TauCeti.idealTerm f s I` is the term `f I / N(I) ^ s` of the ideal-indexed Dirichlet series.
* `TauCeti.idealAbscissaOfAbsConv f` is the abscissa of absolute convergence of that series, the
  ideal-indexed analogue of Mathlib's `LSeries.abscissaOfAbsConv`.

## Main results

* `TauCeti.regroupByNorm`: if the ideal-indexed series has sum `L` at `s`, then so does the
  `LSeries` of `TauCeti.normCoeff f`; `TauCeti.LSeriesSummable_normCoeff` and
  `TauCeti.LSeries_normCoeff` are the summability and value statements it packages.
* `TauCeti.summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re`: weighting the ideal terms
  by `log N(I)` keeps them summable strictly to the right of a point of absolute convergence.
* `TauCeti.abscissaOfAbsConv_normCoeff_le`: consequently the grouped abscissa of absolute
  convergence is at most the ideal-indexed one.
* `TauCeti.summable_idealTerm_of_norm_normCoeff_eq_sum_norm`: the converse holds whenever no
  cancellation occurs inside a norm fibre. `TauCeti.summable_idealTerm_of_nonneg` and
  `TauCeti.idealAbscissaOfAbsConv_eq_abscissaOfAbsConv` specialize it to the case where every
  *individual ideal summand* is nonnegative, where moreover the two abscissae agree.

## Implementation notes

The regrouping is an instance of Mathlib's `HasSum.tsum_fiberwise` along the absolute norm
`fun I ↦ Ideal.absNorm (I : Ideal (𝓞 K))`, whose fibres are the finite sets
`TauCeti.normFiber K n`. Absolute convergence of the ideal-indexed series is expressed as plain
`Summable`, which for a complex-valued family is unconditional convergence and hence absolute
convergence; no rearrangement hypothesis is therefore needed for the transfer.

The converse is proved through `summable_partition` applied to the norms of the terms. All it
needs about `f` is that the norm of each grouped coefficient is the sum of the norms over its
fibre — the absence of cancellation inside the fibre. Nonnegativity of every ideal summand is one
way to secure that, through `TauCeti.norm_normCoeff_eq_sum_norm_of_nonneg`; it is the step that
fails under cancellation, as the rejection test
`TauCeti.exists_forall_normCoeff_nonneg_not_forall_nonneg` records. That test is a statement about
`TauCeti.normCoeff` alone, so it lives with that definition rather than here.

## Roadmap role

This is Layer **1.2** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`; the required worked
example 9 accompanies it in `TauCeti/NumberTheory/ArithmeticDirichletSeries/NormCoeff.lean`. The
exact value of the abscissa for the trivial weight is deliberately not proved here: its divergence
input is the Layer 5 ideal count of
`TauCeti/NumberTheory/ArithmeticDirichletSeries/Estimates.lean`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters II--III.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open scoped _root_.nonZeroDivisors _root_.NumberField _root_.ComplexOrder

variable (K : Type*) [Field K] [NumberField K]

/-! ### The ideal-indexed term -/



/-- Defining equation of `TauCeti.idealTerm`. -/
theorem TauCeti.idealTerm_def (f : _root_.TauCeti.IdealArithmeticFunction K) (s : ℂ) (I : (_root_.Ideal (𝓞 K))⁰) :
    _root_.TauCeti.idealTerm K f s I = f I / (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℂ) ^ s :=
  (_root_.rfl)

/-- The absolute value of an ideal term depends on `s` only through its real part. -/
@[simp]
theorem TauCeti.norm_idealTerm (f : _root_.TauCeti.IdealArithmeticFunction K) (s : ℂ) (I : (_root_.Ideal (𝓞 K))⁰) :
    ‖_root_.TauCeti.idealTerm K f s I‖ = ‖f I‖ / (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ) ^ s.re := by
  rw [_root_.TauCeti.idealTerm_def, _root_.norm_div,
    _root_.Complex.norm_natCast_cpow_of_pos (_root_.Ideal.absNorm_pos_of_nonZeroDivisors I)]







/-- **Log-weighted ideal terms stay summable strictly to the right.**  If the ideal-indexed
Dirichlet series of `f` converges absolutely at `s`, then weighting each term by `log N(I)` leaves
it summable at every `s'` with `Re s < Re s'`.

The strict inequality is what separates this from `summable_idealTerm_of_re_le_re`, which
propagates unweighted convergence along `Re s ≤ Re s'`: the logarithmic weight can destroy
summability at `Re s' = Re s`.  This is the ideal-indexed counterpart of Mathlib's
`LSeriesSummable_logMul_of_lt_re`, and the logarithmic weight is what appears when the terms are
differentiated in `s`. -/
theorem solution
    {f : _root_.TauCeti.IdealArithmeticFunction K} {s s' : ℂ}
    (h : s.re < s'.re) (hs : _root_.Summable (_root_.TauCeti.idealTerm K f s)) :
    _root_.Summable fun I : (_root_.Ideal (𝓞 K))⁰ ↦
      _root_.Real.log (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K))) * ‖_root_.TauCeti.idealTerm K f s' I‖ := by
  have hδ : 0 < s'.re - s.re := _root_.sub_pos.2 h
  refine _root_.Summable.of_nonneg_of_le (fun I ↦ ?_) (fun I ↦ ?_)
    ((_root_.summable_norm_iff.2 hs).mul_left (s'.re - s.re)⁻¹)
  · have h1 : (1:ℝ) ≤ (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ) := by
      exact_mod_cast _root_.Ideal.absNorm_pos_of_nonZeroDivisors I
    exact _root_.mul_nonneg (_root_.Real.log_nonneg h1) (_root_.norm_nonneg _)
  · have hN : (0:ℝ) < (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ) := by
      exact_mod_cast _root_.Ideal.absNorm_pos_of_nonZeroDivisors I
    rw [_root_.TauCeti.norm_idealTerm, _root_.TauCeti.norm_idealTerm]
    -- `log x ≤ x ^ δ / δ` with `δ = Re s' - Re s`; the extra `N(I) ^ δ` is exactly what turns the
    -- term at `s'` into the term at `s`.
    have hlog := _root_.Real.log_le_rpow_div hN.le hδ
    rw [_root_.Real.rpow_sub hN] at hlog
    calc _root_.Real.log (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ)
            * (‖f I‖ / (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ) ^ s'.re)
        ≤ ((_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ) ^ s'.re
            / (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ) ^ s.re / (s'.re - s.re))
            * (‖f I‖ / (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ) ^ s'.re) := by
          gcongr
      _ = (s'.re - s.re)⁻¹ * (‖f I‖ / (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ) ^ s.re) := by
          field_simp

/-! ### Regrouping -/











/-! ### The ideal-indexed abscissa of absolute convergence -/













/-! ### The converse, in the absence of cancellation inside norm fibres -/











end TauCeti

end
end
