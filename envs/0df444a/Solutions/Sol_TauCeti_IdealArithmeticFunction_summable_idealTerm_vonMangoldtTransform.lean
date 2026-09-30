-- Prove2me | solution 1 for TauCeti.IdealArithmeticFunction.summable_idealTerm_vonMangoldtTransform
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:25:24.869786+00:00
-- url     : https://prove2.me/submissions/c2007d39-625f-4e9b-b411-cb4df654b773

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Data
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Regroup
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_VonMangoldt
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real
import Theorems.Thm_TauCeti_IdealArithmeticFunction_norm_vonMangoldt_le_log
import Theorems.Thm_TauCeti_summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re

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

open scoped _root_.nonZeroDivisors _root_.NumberField _root_.ComplexOrder

variable (K : Type*) [Field K] [NumberField K]

/-! ### The ideal-indexed term -/



/-- Defining equation of `TauCeti.idealTerm`. -/
theorem idealTerm_def (f : IdealArithmeticFunction K) (s : ℂ) (I : (Ideal (𝓞 K))⁰) :
    idealTerm K f s I = f I / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ s :=
  (rfl)











/-! ### Regrouping -/











/-! ### The ideal-indexed abscissa of absolute convergence -/



/-- Defining equation of `TauCeti.idealAbscissaOfAbsConv`. -/
theorem idealAbscissaOfAbsConv_def (f : IdealArithmeticFunction K) :
    idealAbscissaOfAbsConv K f = sInf (Real.toEReal '' {x : ℝ | Summable (idealTerm K f x)}) :=
  (rfl)









/-! ### The converse, in the absence of cancellation inside norm fibres -/











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
# The ideal von Mangoldt function

The von Mangoldt function of a nonzero ideal `A` of the ring of integers of a number field is
`log N(P)` when `A` is a positive power of a prime ideal `P`, and zero otherwise.  This file
packages that function as an `IdealArithmeticFunction` and defines its pointwise product with an
ideal arithmetic function.

## Main definitions

* `TauCeti.IdealArithmeticFunction.vonMangoldt` is the complex-valued ideal von Mangoldt
  function.
* `TauCeti.IdealArithmeticFunction.vonMangoldtTransform` sends `f` to the weighted function
  `A ↦ f(A) Λ(A)`.

## Main results

* `TauCeti.IdealArithmeticFunction.vonMangoldt_apply_prime_pow` computes the value on a positive
  power of a prime ideal.
* `TauCeti.IdealArithmeticFunction.vonMangoldt_ne_zero_iff` says that its support is exactly the
  prime-power ideals.
* `TauCeti.IdealArithmeticFunction.vonMangoldtTransform_ne_zero_iff` identifies the support of
  the transform, and its specialization in `TauCeti.MultiplicativeIdealWeight` describes this as
  the good prime powers for a completely multiplicative weight.

The definition chooses a prime base from a proof that `A` is a prime power.  Mathlib's
`eq_of_prime_pow_eq`, applied to ideals, identifies that choice with any prime base supplied by a
caller.  The public evaluation theorem therefore removes the choice from every computation.

## Implementation notes

This is the ideal analogue of Mathlib's `ArithmeticFunction.vonMangoldt`.  Here the prime base is
chosen from `IsPrimePow` rather than computed by `Nat.minFac`, its logarithmic weight is
`Ideal.absNorm P` rather than `p`, and the function is complex-valued to match
`IdealArithmeticFunction`.

## Roadmap role

This is the algebraic part of Layer **2.3** of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.  The logarithmic-derivative identity named in
that target additionally requires the Euler-product package of Layer 3; this file supplies its
coefficient and exact prime-power support in advance.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
-/

 section

namespace TauCeti

open _root_.NumberField
open scoped _root_.nonZeroDivisors _root_.NumberField

variable {K : Type*} [Field K] [NumberField K]



namespace IdealArithmeticFunction



























/-- Evaluation of the von Mangoldt transform. -/
theorem vonMangoldtTransform_apply (f : IdealArithmeticFunction K)
    (A : (Ideal (𝓞 K))⁰) :
    f.vonMangoldtTransform A = f A * vonMangoldt A := by
  rw [vonMangoldtTransform, Pi.mul_apply]







end IdealArithmeticFunction

namespace MultiplicativeIdealWeight





end MultiplicativeIdealWeight

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
# The logarithmic derivative as a von Mangoldt Dirichlet series

Strictly to the right of the abscissa of absolute convergence,

`logDeriv L(s) = -∑' A, χ(A) Λ(A) / N(A) ^ s`,

the sum running over the nonzero integral ideals of `𝓞 K`, with `Λ` the ideal von Mangoldt
function. This is the coefficient identity: it names the exact Dirichlet coefficients of the
logarithmic derivative, which is what a Tauberian argument consumes.

The prime-power expansion of `logDeriv_LSeries_eq_tsum_prime_pow` is the same sum written over
`(𝔭, k)`. The two agree termwise, because the von Mangoldt transform of a completely multiplicative
weight at `𝔭 ^ (k+1)` is `χ(𝔭) ^ (k+1) log N(𝔭)` and `N(𝔭 ^ (k+1)) = N(𝔭) ^ (k+1)`; the transform
vanishes off the prime powers, so nothing else contributes.

For general Euler-product data `D`, whose values at higher prime powers are independent, the
coefficient at `𝔭 ^ e` is `log N(𝔭)` times the degree-`e` coefficient of the local series
`X F_𝔭'/F_𝔭`. This defines the von Mangoldt function `Λ_D` of `D`, which is the von Mangoldt
transform of the weight in the completely multiplicative case. Where the local power series are
zero-free on the disks of absolute convergence, `-logDeriv L(s) = ∑' A, Λ_D(A) / N(A) ^ s`, with
absolute convergence.

## Main definitions

* `TauCeti.EulerProductData.vonMangoldt`: the von Mangoldt function `Λ_D` of Euler-product data.

## Main results

* `TauCeti.IdealArithmeticFunction.summable_idealTerm_vonMangoldtTransform`: the von Mangoldt
  weighted ideal terms are summable on the half-plane, for any ideal arithmetic function.
* `TauCeti.MultiplicativeIdealWeight.logDeriv_LSeries_eq_neg_tsum_vonMangoldtTransform`: the
  coefficient identity for a completely multiplicative weight.
* `TauCeti.EulerProductData.vonMangoldt_ofMultiplicativeIdealWeight`: `Λ_D` of a completely
  multiplicative weight is its von Mangoldt transform.
* `TauCeti.EulerProductData.hasSum_idealTerm_vonMangoldt_of_zeroFree` and
  `TauCeti.EulerProductData.LSeriesHasSum_normCoeff_vonMangoldt_of_zeroFree`: the coefficient
  identity for general Euler-product data, ideal-indexed and regrouped by norm.

## Implementation notes

Summability is comparison against `TauCeti.summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re`,
whose weight `log N(I)` dominates `‖Λ(I)‖` by `norm_vonMangoldt_le_log`. Passing from the
`(𝔭, k)`-indexed sum to the ideal-indexed one is
`TauCeti.tsum_eq_tsum_idealPrimePower_of_support_subset`.

For general `D`, `PowerSeries.tsum_norm_coeff_logDeriv_mul_pow_succ_le` supplies the local
majorant that gives absolute convergence of the von Mangoldt series. The general coefficient
identity applies to data with an absolute-convergence point `σ` and zero-free local series on the
corresponding disks.

## References

* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, §5.1, for the von Mangoldt function of
  a general Euler product.
-/

 section

open scoped nonZeroDivisors NumberField
open IsDedekindDomain NumberField

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

namespace TauCeti.IdealArithmeticFunction
end TauCeti.IdealArithmeticFunction
section IdealArithmeticFunction
open TauCeti TauCeti.IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K]

/-- **The von Mangoldt weighted ideal terms converge absolutely.** Strictly to the right of the
abscissa of absolute convergence of `χ`, the terms `χ(A) Λ(A) / N(A) ^ s` are summable.

`Λ(A)` is bounded by `log N(A)`, and weighting the ideal terms by `log N(A)` preserves summability
strictly to the right of a point of absolute convergence. -/
theorem solution {f : _root_.TauCeti.IdealArithmeticFunction K} {s : ℂ}
    (hs : _root_.TauCeti.idealAbscissaOfAbsConv K f < s.re) :
    _root_.Summable (_root_.TauCeti.idealTerm K f.vonMangoldtTransform s) := by
  obtain ⟨y, hy, hys⟩ : ∃ y : ℝ, _root_.Summable (_root_.TauCeti.idealTerm K f y) ∧ y < s.re := by
    simpa [_root_.TauCeti.idealAbscissaOfAbsConv_def, _root_.sInf_lt_iff] using hs
  have hlog := _root_.TauCeti.summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re
    (f := f) (s := (y : ℂ)) (s' := s) (h := by simpa using hys) (hs := hy)
  refine hlog.of_norm_bounded fun A ↦ ?_
  have hfac : ‖_root_.TauCeti.idealTerm K f.vonMangoldtTransform s A‖
      = ‖(_root_.TauCeti.IdealArithmeticFunction.vonMangoldt : _root_.TauCeti.IdealArithmeticFunction K) A‖
        * ‖_root_.TauCeti.idealTerm K f s A‖ := by
    rw [_root_.TauCeti.idealTerm_def, _root_.TauCeti.idealTerm_def, _root_.TauCeti.IdealArithmeticFunction.vonMangoldtTransform_apply,
      _root_.norm_div, _root_.norm_div, _root_.norm_mul]
    ring
  rw [hfac]
  exact _root_.mul_le_mul_of_nonneg_right
    (_root_.TauCeti.IdealArithmeticFunction.norm_vonMangoldt_le_log A) (_root_.norm_nonneg _)

end IdealArithmeticFunction

namespace TauCeti.MultiplicativeIdealWeight
end TauCeti.MultiplicativeIdealWeight
section MultiplicativeIdealWeight
open TauCeti TauCeti.MultiplicativeIdealWeight

variable {K : Type*} [Field K] [NumberField K] (χ : MultiplicativeIdealWeight K)






end MultiplicativeIdealWeight

namespace TauCeti.EulerProductData
end TauCeti.EulerProductData
section EulerProductData
open TauCeti TauCeti.EulerProductData

variable {K : Type*} [Field K] [NumberField K] (D : EulerProductData K)









section Analytic

variable {σ : ℝ} {s : ℂ}















end Analytic

end EulerProductData

end TauCeti

end
end
