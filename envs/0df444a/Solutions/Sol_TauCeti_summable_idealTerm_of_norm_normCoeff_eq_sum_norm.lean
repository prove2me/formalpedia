-- Prove2me | solution 1 for TauCeti.summable_idealTerm_of_norm_normCoeff_eq_sum_norm
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:16:18.901944+00:00
-- url     : https://prove2.me/submissions/491f09a8-fe7d-4d37-8dde-157ff1a881b0

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_NormCoeff
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
# Regrouping ideal arithmetic functions by absolute norm

This file defines `TauCeti.normCoeff`, the ordinary arithmetic function obtained by summing an
`IdealArithmeticFunction` over each fibre of the absolute norm.  These fibres are finite by
`Ideal.finite_setOfPred_absNorm_eq`, so the coefficients are honest finite sums.  The resulting
function has value zero at `0`, as required by Mathlib's `ArithmeticFunction` carrier; that value
is available from `ArithmeticFunction.map_zero`.

The construction is bundled as a complex-linear map.  The basic API exposes the finite norm fibre
`TauCeti.normFiber` and its finiteness, records the value at one, proves compatibility with
complex conjugation, and records in `TauCeti.norm_normCoeff_eq_sum_norm_of_nonneg` that no
cancellation occurs inside a fibre when the values of `f` are nonnegative.  Regrouping is
compatible with transporting along an isomorphism of number fields: `TauCeti.normCoeff_map` says
that an isomorphism `e : K ≃+* L` leaves every norm coefficient unchanged.

Regrouping loses information as soon as a norm fibre has more than one element:
`TauCeti.exists_forall_normCoeff_nonneg_not_forall_nonneg` produces a nonzero ideal arithmetic
function, with a negative value, whose norm coefficients all vanish.  This is the rejection test
that forbids weakening the nonnegativity hypothesis of the converse regrouping theorem to
nonnegativity of the coefficients themselves.

## Roadmap role

This is the finite-norm-fibre part of Layer **1.1** of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.  The next layer step uses these coefficients
to regroup an absolutely convergent series over nonzero ideals into a Mathlib `LSeries`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters II--III.
-/

 section

namespace TauCeti

open scoped _root_.nonZeroDivisors _root_.NumberField _root_.ComplexOrder

variable (K : Type*) [Field K] [NumberField K]







/-- The absolute-norm fibre, viewed as a set, is the preimage of `{n}` under the absolute norm. -/
theorem coe_normFiber (n : ℕ) :
    (normFiber K n : Set ((Ideal (𝓞 K))⁰))
      = (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) ⁻¹' {n} := by
  ext I
  simp

























/-! ### The cancellation rejection test -/



end TauCeti

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

/-- Ideal terms decrease in absolute value as the real part of `s` grows, because every nonzero
integral ideal has absolute norm at least one. -/
theorem TauCeti.norm_idealTerm_le_of_re_le_re (f : _root_.TauCeti.IdealArithmeticFunction K) {s s' : ℂ}
    (h : s.re ≤ s'.re) (I : (_root_.Ideal (𝓞 K))⁰) :
    ‖_root_.TauCeti.idealTerm K f s' I‖ ≤ ‖_root_.TauCeti.idealTerm K f s I‖ := by
  have h₁ : (1 : ℝ) ≤ (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ) := by
    exact_mod_cast _root_.Ideal.absNorm_pos_of_nonZeroDivisors I
  have h₀ : (0 : ℝ) < (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ) ^ s.re :=
    _root_.Real.rpow_pos_of_pos (by linarith) _
  simp only [_root_.TauCeti.norm_idealTerm]
  gcongr

/-- Absolute convergence of the ideal-indexed series propagates to the right. -/
theorem TauCeti.summable_idealTerm_of_re_le_re {f : _root_.TauCeti.IdealArithmeticFunction K} {s s' : ℂ}
    (h : s.re ≤ s'.re) (hf : _root_.Summable (_root_.TauCeti.idealTerm K f s)) : _root_.Summable (_root_.TauCeti.idealTerm K f s') := by
  rw [← _root_.summable_norm_iff] at hf ⊢
  exact hf.of_nonneg_of_le (fun _ ↦ _root_.norm_nonneg _) (_root_.TauCeti.norm_idealTerm_le_of_re_le_re K f h)

/-- Absolute convergence of the ideal-indexed series depends on `s` only through its real part. -/
theorem TauCeti.summable_idealTerm_iff_of_re_eq_re {f : _root_.TauCeti.IdealArithmeticFunction K} {s s' : ℂ}
    (h : s.re = s'.re) : _root_.Summable (_root_.TauCeti.idealTerm K f s) ↔ _root_.Summable (_root_.TauCeti.idealTerm K f s') :=
  ⟨_root_.TauCeti.summable_idealTerm_of_re_le_re K h.le, _root_.TauCeti.summable_idealTerm_of_re_le_re K h.ge⟩



/-! ### Regrouping -/











/-! ### The ideal-indexed abscissa of absolute convergence -/













/-! ### The converse, in the absence of cancellation inside norm fibres -/



/-- In the absence of cancellation inside norm fibres, the sum over an absolute-norm fibre of the
absolute values of the ideal terms at a real `x` is the absolute value of the corresponding
`LSeries` term. This is the step of the converse regrouping that cancellation destroys. -/
private theorem TauCeti.tsum_norm_idealTerm_fiber (f : _root_.TauCeti.IdealArithmeticFunction K)
    (hf : ∀ n, ‖_root_.TauCeti.normCoeff K f n‖ = ∑ I ∈ _root_.TauCeti.normFiber K n, ‖f I‖) (x : ℝ) (n : ℕ) :
    ∑' I : (fun I : (_root_.Ideal (𝓞 K))⁰ ↦ _root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K))) ⁻¹' {n},
        ‖_root_.TauCeti.idealTerm K f x I‖ = ‖_root_.LSeries.term (_root_.TauCeti.normCoeff K f) x n‖ := by
  rw [← _root_.TauCeti.coe_normFiber, _root_.Finset.tsum_subtype' (_root_.TauCeti.normFiber K n) fun I ↦ ‖_root_.TauCeti.idealTerm K f x I‖]
  rcases _root_.eq_or_ne n 0 with rfl | hn
  · simp
  rw [_root_.LSeries.term_of_ne_zero hn, _root_.norm_div,
    _root_.Complex.norm_natCast_cpow_of_pos (_root_.Nat.pos_of_ne_zero hn), hf n, _root_.Finset.sum_div]
  refine _root_.Finset.sum_congr _root_.rfl fun I hI ↦ ?_
  rw [_root_.TauCeti.norm_idealTerm, (_root_.TauCeti.mem_normFiber K).mp hI]

/-- **The converse regrouping, in the absence of cancellation inside norm fibres.** If the
absolute value of every grouped coefficient is the sum of the absolute values of `f` over the
corresponding fibre — that is, if adding up a fibre loses no absolute value — then absolute
convergence of the regrouped `LSeries` implies absolute convergence of the ideal-indexed series.

This is the hypothesis the proof actually uses: it holds for a nonnegative `f`, by
`TauCeti.norm_normCoeff_eq_sum_norm_of_nonneg`, but equally for a uniformly negative one or, more
generally, whenever the values of `f` over each fibre share a common phase. Nonnegativity of the
*grouped* coefficients `TauCeti.normCoeff f` does not suffice; see
`TauCeti.exists_forall_normCoeff_nonneg_not_forall_nonneg`. -/
theorem solution (f : _root_.TauCeti.IdealArithmeticFunction K)
    (hf : ∀ n, ‖_root_.TauCeti.normCoeff K f n‖ = ∑ I ∈ _root_.TauCeti.normFiber K n, ‖f I‖) {s : ℂ}
    (h : _root_.LSeriesSummable (_root_.TauCeti.normCoeff K f) s) : _root_.Summable (_root_.TauCeti.idealTerm K f s) := by
  rw [_root_.TauCeti.summable_idealTerm_iff_of_re_eq_re K (s' := (s.re : ℂ)) (by simp)]
  replace h : _root_.LSeriesSummable (_root_.TauCeti.normCoeff K f) (s.re : ℂ) := h.of_re_le_re (by simp)
  refine _root_.Summable.of_norm ?_
  rw [_root_.summable_partition (f := fun I ↦ ‖_root_.TauCeti.idealTerm K f (s.re : ℂ) I‖) (fun _ ↦ _root_.norm_nonneg _)
    (s := fun n ↦ (fun I : (_root_.Ideal (𝓞 K))⁰ ↦ _root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K))) ⁻¹' {n})
    fun I ↦ ⟨_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)), _root_.rfl, fun _ hn ↦ hn.symm⟩]
  refine ⟨fun n ↦ ?_, ?_⟩
  · have : _root_.Finite ((fun I : (_root_.Ideal (𝓞 K))⁰ ↦ _root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K))) ⁻¹' {n}) :=
      (_root_.TauCeti.finite_normFiber K n).to_subtype
    exact _root_.Summable.of_finite
  · exact (summable_norm_iff.mpr h).congr fun n ↦
      (_root_.TauCeti.tsum_norm_idealTerm_fiber K f hf s.re n).symm





end TauCeti

end
end
