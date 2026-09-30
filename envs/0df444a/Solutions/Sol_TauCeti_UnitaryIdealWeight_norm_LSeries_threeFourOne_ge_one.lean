-- Prove2me | solution 1 for TauCeti.UnitaryIdealWeight.norm_LSeries_threeFourOne_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:56:07.905985+00:00
-- url     : https://prove2.me/submissions/bea2e20d-a2c8-441f-b73b-43da162f2dd0

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Analysis_SpecialFunctions_Trigonometric_NonnegCombination
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Analytic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Data
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_NormCoeff
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Regroup
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_NumberTheory_LSeries_ThreeFourOne
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Ideal
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Convolution
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
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real
import Theorems.Thm_TauCeti_EulerProductData_eulerFactor_eq_tsum
import Theorems.Thm_TauCeti_EulerProductData_hasProd_eulerFactor
import Theorems.Thm_TauCeti_LSeriesSummable_normCoeff_one_iff
import Theorems.Thm_TauCeti_MultiplicativeIdealWeight_apply_ne_zero_iff_isGood
import Theorems.Thm_TauCeti_sum_re_neg_log_one_sub_nonneg
import Theorems.Thm_TauCeti_summable_idealTerm_of_norm_normCoeff_eq_sum_norm

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Nonnegative trigonometric combinations

This file packages finite trigonometric combinations that are nonnegative on the complex unit
circle. It also transfers their pointwise nonnegativity to the closed unit disk and the Taylor
series of `-log (1 - z)`, giving a reusable logarithmic inequality.

## Main declarations

* `TauCeti.trigonometricCombination` is a finite weighted cosine combination.
* `TauCeti.IsNonnegativeTrigonometricCombination` asserts nonnegativity on the unit circle.
* `TauCeti.trigonometricCombination_nonneg_of_boundary` extends this nonnegativity to the closed
  unit disk.
* `TauCeti.sum_re_neg_log_one_sub_nonneg` transfers boundary nonnegativity to logarithms in the
  open unit disk.

## Provenance

The logarithmic transfer generalizes the private lemma `re_log_comb_nonneg'` in the
`DirichletCharacter` namespace of Mathlib's
`Mathlib/NumberTheory/LSeries/Nonvanishing.lean`, due to Michael Stoll and David Loeffler, from
the fixed `3-4-1` weights to an arbitrary finite nonnegative combination.

This is part of Layer 8.2 of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.
-/

 section

namespace TauCeti

open Complex

noncomputable section

variable {ι : Type*}



/-- The defining finite-sum formula for `trigonometricCombination`. -/
theorem trigonometricCombination_def (s : Finset ι) (c : ι → ℝ) (m : ι → ℕ) (z : ℂ) :
    trigonometricCombination s c m z = ∑ i ∈ s, c i * (z ^ m i).re := (rfl)



variable {s : Finset ι} {c : ι → ℝ} {m : ι → ℕ}





end

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







/-- The value of `normCoeff f` is the finite sum of `f` over the corresponding absolute-norm
fibre. -/
theorem normCoeff_apply (f : IdealArithmeticFunction K) (n : ℕ) :
    normCoeff K f n =
      ∑ᶠ I ∈ {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = n}, f I :=
  (rfl)

/-- The value of `normCoeff f` as a sum over the finite absolute-norm fibre. -/
theorem normCoeff_eq_sum_normFiber (f : IdealArithmeticFunction K) (n : ℕ) :
    normCoeff K f n = ∑ I ∈ normFiber K n, f I := by
  rw [normCoeff_apply, finsum_mem_eq_finite_toFinset_sum _ (finite_normFiber K n)]
  simp only [normFiber]













/-- **Absence of cancellation inside norm fibres**, for a nonnegative ideal arithmetic function:
the absolute value of a norm coefficient is the sum of the absolute values over the fibre. -/
theorem norm_normCoeff_eq_sum_norm_of_nonneg (f : IdealArithmeticFunction K) (hf : ∀ I, 0 ≤ f I)
    (n : ℕ) : ‖normCoeff K f n‖ = ∑ I ∈ normFiber K n, ‖f I‖ := by
  have h : normCoeff K f n = ((∑ I ∈ normFiber K n, ‖f I‖ : ℝ) : ℂ) := by
    rw [normCoeff_eq_sum_normFiber]
    push_cast
    exact Finset.sum_congr rfl fun I _ ↦ Complex.eq_coe_norm_of_nonneg (hf I)
  rw [h, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]

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
# Completely multiplicative ideal weights

The completely multiplicative specializations of `TauCeti.IdealArithmeticFunction`: the two
carriers on which every Euler product, Hecke character and character-family argument of this
development is stated.

A `TauCeti.MultiplicativeIdealWeight K` is a monoid-with-zero homomorphism
`Ideal (𝓞 K) →*₀ ℂ` killing only finitely many height-one primes, and
`TauCeti.UnitaryIdealWeight K` is the subtype of those whose values have modulus `1` away from
that finite bad set. Using Mathlib's `→*₀` vocabulary is what pins the zero-ideal law
`χ ⊥ = 0`; the finiteness condition is what bounds the bad local factors of the Euler product.

Both carriers are *degree one*: the value at `𝔭 ^ n` is forced to be `χ 𝔭 ^ n`. They are
therefore deliberately too narrow for the ideal Möbius function or for coefficient systems
whose prime-power values are independent local data; those get separate carriers.

The organising notion is `Ideal.IsPrimeTo`, an ideal of a Dedekind domain being nonzero and
divisible by no prime of a given set; it is stated for a general Dedekind domain because
nothing in it is specific to a number field. The good ideals of a weight are the ideals
prime to its bad primes, and `Ideal.IsPrimeTo.induction_on` factors such an ideal into
good primes; this is the engine behind both
`TauCeti.MultiplicativeIdealWeight.apply_ne_zero_iff_isGood` and
`TauCeti.UnitaryIdealWeight.norm_eq_one`.

## Main declarations

* `Ideal.IsPrimeTo`: an ideal is nonzero and no prime of `S` divides it, with its
  multiplicativity (`Ideal.isPrimeTo_mul_iff`) and its induction principle
  (`Ideal.IsPrimeTo.induction_on`);
* `TauCeti.MultiplicativeIdealWeight`: the general completely multiplicative carrier, its
  `TauCeti.MultiplicativeIdealWeight.badPrimes` and its good ideals
  (`TauCeti.MultiplicativeIdealWeight.IsGood`);
* `TauCeti.MultiplicativeIdealWeight.apply_ne_zero_iff_isGood`: a weight is nonzero exactly on
  the good ideals;
* `TauCeti.MultiplicativeIdealWeight.ext_heightOneSpectrum`: a weight is determined by its
  values at the height-one primes;
* `TauCeti.MultiplicativeIdealWeight.ofBadPrimes`, the pointwise `CommMonoid` structure (whose
  unit is the trivial weight), `TauCeti.MultiplicativeIdealWeight.restrict`,
  `TauCeti.MultiplicativeIdealWeight.conj` and
  `TauCeti.MultiplicativeIdealWeight.normTwist`: the constructors and operations;
* `TauCeti.MultiplicativeIdealWeight.IsNormTwistOnGood` and
  `TauCeti.MultiplicativeIdealWeight.IsTrivialOnGood`: the weights agreeing with a purely
  imaginary norm twist, respectively with the trivial weight, on their good ideals, with the
  structure theorem `TauCeti.MultiplicativeIdealWeight.IsNormTwistOnGood.eq_normTwist`, its
  converse `TauCeti.MultiplicativeIdealWeight.isNormTwistOnGood_normTwist_ofBadPrimes`, and the
  behaviour of the parameter under conjugation, the pointwise product and a further twist;
* `TauCeti.MultiplicativeIdealWeight.toIdealArithmeticFunction`: passage to the general
  carrier, inverted by `TauCeti.IdealArithmeticFunction.zeroExtend`;
* `TauCeti.UnitaryIdealWeight`: the unitary subtype, with
  `TauCeti.UnitaryIdealWeight.norm_eq_one` on all good ideals,
  `TauCeti.UnitaryIdealWeight.norm_normTwist` for the modulus of an arbitrary norm twist,
  `TauCeti.UnitaryIdealWeight.ofPowEqOne` for finite-order weights, and the operations
  `TauCeti.UnitaryIdealWeight.conj`, `TauCeti.UnitaryIdealWeight.restrict` and
  `TauCeti.UnitaryIdealWeight.normTwist` (the last for the imaginary norm twists only), and
  `TauCeti.UnitaryIdealWeight.toIdealArithmeticFunction` for its passage to the general carrier;
* `TauCeti.MultiplicativeIdealWeight.map` and `TauCeti.UnitaryIdealWeight.map`, with their
  equivalences `mapEquiv`: functoriality under an isomorphism `K ≃+* L` of the ambient fields,
  together with the identity and composition laws, the preservation of the pointwise product
  (`map_one` and `map_mul` on both carriers), the naturality of restriction, conjugation and norm
  twists, and the compatibilities
  `TauCeti.MultiplicativeIdealWeight.badPrimes_map` and
  `TauCeti.MultiplicativeIdealWeight.toIdealArithmeticFunction_map`.

## Rejection tests

The two worked negative examples of this layer are proved here.
`TauCeti.MultiplicativeIdealWeight.coe_ne_const_one` says the everywhere-one function on *all*
integral ideals underlies no weight, because `→*₀` forces the value `0` at `⊥` — the
everywhere-one function on the *nonzero* ideals is the trivial weight instead
(`TauCeti.MultiplicativeIdealWeight.toIdealArithmeticFunction_one`).
`TauCeti.UnitaryIdealWeight.norm_normTwist_apply_ne_one` says that a norm twist with
`Re z ≠ 0` changes the modulus at every good ideal of absolute norm greater than one, so such
twists live only in the general carrier.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* `TauCetiRoadmap/ArithmeticDirichletSeries/README.md` and its `Suggested.lean` target
  signatures: this file implements the Layer 0 export contract stated there, and follows its
  naming and organization for the two weight carriers.
-/

 section

namespace TauCeti

open _root_.NumberField _root_.IsDedekindDomain _root_.nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]



/-!
### The general carrier of completely multiplicative ideal weights
-/



namespace MultiplicativeIdealWeight





















variable {χ : MultiplicativeIdealWeight K}





theorem apply_eq_zero_iff_not_isGood (χ : MultiplicativeIdealWeight K) (I : Ideal (𝓞 K)) :
    χ I = 0 ↔ ¬ χ.IsGood I := by
  rw [← not_ne_iff, χ.apply_ne_zero_iff_isGood]

/-!
### Constructors and operations
-/

section Operations

variable {S : Set (HeightOneSpectrum (𝓞 K))}























/-- A positive power of a weight is computed pointwise. The exponent must be nonzero: `χ ^ 0` is
the trivial weight, which vanishes at `⊥`, while `χ ⊥ ^ 0 = 1`. -/
@[simp]
theorem pow_apply (χ : MultiplicativeIdealWeight K) {n : ℕ} (hn : n ≠ 0) (I : Ideal (𝓞 K)) :
    (χ ^ n) I = χ I ^ n := by
  induction n with
  | zero => exact absurd rfl hn
  | succ n ih =>
    rcases eq_or_ne n 0 with rfl | h
    · rw [zero_add, pow_one, pow_one]
    · rw [pow_succ, pow_succ, mul_apply, ih h]

































/-!
### Weights that are norm twists on their good locus
-/





/-- A weight trivial on its good ideals takes the value `1` at each of them. -/
@[simp]
theorem IsTrivialOnGood.apply_eq_one {χ : MultiplicativeIdealWeight K} (h : χ.IsTrivialOnGood)
    {I : Ideal (𝓞 K)} (hI : χ.IsGood I) : χ I = 1 :=
  h I hI

/-- A weight trivial on its good ideals takes only the values `0` and `1`, so it is bounded by one
on every ideal. -/
theorem IsTrivialOnGood.norm_apply_le_one {χ : MultiplicativeIdealWeight K}
    (h : χ.IsTrivialOnGood) {I : Ideal (𝓞 K)} : ‖χ I‖ ≤ 1 := by
  by_cases hI : χ.IsGood I
  · rw [h.apply_eq_one hI, norm_one]
  · rw [(χ.apply_eq_zero_iff_not_isGood I).mpr hI, norm_zero]
    exact zero_le_one

















end Operations

/-!
### Passage to the general carrier, and the zero-ideal rejection test
-/



















/-!
### Functoriality under an isomorphism of fields
-/

section Transport

variable {L M : Type*} [Field L] [NumberField L] [Field M] [NumberField M]





















/-! Transport preserves the pointwise `CommMonoid` structure. -/













end Transport

end MultiplicativeIdealWeight

/-!
### The unitary subtype
-/



namespace UnitaryIdealWeight

/-- **A unitary weight has modulus one on every good ideal**, extending its defining condition
from good primes to the entire good-ideal locus. -/
theorem norm_eq_one (χ : UnitaryIdealWeight K) {I : Ideal (𝓞 K)} (hI : χ.1.IsGood I) :
    ‖χ.1 I‖ = 1 := by
  refine hI.induction_on (by simp) fun 𝔭 J h𝔭 _ ih ↦ ?_
  rw [map_mul, norm_mul, χ.2 𝔭 h𝔭, ih, one_mul]

-- Source. The statement and its proof follow `DirichletCharacter.norm_le_one` in Mathlib's
-- `Mathlib/NumberTheory/DirichletCharacter/Bounds.lean`, transposed from a Dirichlet character on
-- `ZMod n` to a unitary ideal weight: the case split there is on `IsUnit a` and closes with
-- `map_nonunit`, here it is on `MultiplicativeIdealWeight.IsGood` and closes with
-- `apply_eq_zero_iff_not_isGood`.

/-- **A unitary weight is bounded by one on every ideal.** The bound is unconditional: it carries
no goodness hypothesis, so a comparison indexed by all of `(Ideal (𝓞 K))⁰` can apply it termwise.
`norm_eq_one` is sharper where it applies, but obliges the caller to split that index type first;
this is the form a convergence estimate wants. -/
theorem norm_le_one (χ : UnitaryIdealWeight K) (I : Ideal (𝓞 K)) : ‖χ.1 I‖ ≤ 1 := by
  by_cases hI : χ.1.IsGood I
  · exact (norm_eq_one χ hI).le
  · rw [(MultiplicativeIdealWeight.apply_eq_zero_iff_not_isGood χ.1 I).mpr hI, norm_zero]
    exact zero_le_one











@[simp]
theorem val_pow (χ : UnitaryIdealWeight K) (n : ℕ) : (χ ^ n).1 = χ.1 ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, val_one]
  | succ n ih => rw [pow_succ, pow_succ, val_mul, ih]



























section Transport

variable {L M : Type*} [Field L] [NumberField L] [Field M] [NumberField M]















/-! Transport preserves the pointwise `CommMonoid` structure of the unitary carrier too. -/











end Transport



@[simp]
theorem toIdealArithmeticFunction_apply (χ : UnitaryIdealWeight K) (I : (Ideal (𝓞 K))⁰) :
    χ.toIdealArithmeticFunction I = χ.1 I := (rfl)

/-- The ideal arithmetic function of a unitary weight agrees with that of its underlying
multiplicative weight. -/
theorem toIdealArithmeticFunction_eq_val (χ : UnitaryIdealWeight K) :
    χ.toIdealArithmeticFunction = χ.1.toIdealArithmeticFunction := by
  funext I
  rw [toIdealArithmeticFunction_apply,
    MultiplicativeIdealWeight.toIdealArithmeticFunction_apply]











end UnitaryIdealWeight

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

open scoped _root_.nonZeroDivisors _root_.NumberField _root_.ComplexOrder

variable (K : Type*) [Field K] [NumberField K]

/-! ### The ideal-indexed term -/



/-- Defining equation of `TauCeti.idealTerm`. -/
theorem idealTerm_def (f : IdealArithmeticFunction K) (s : ℂ) (I : (Ideal (𝓞 K))⁰) :
    idealTerm K f s I = f I / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ s :=
  (rfl)

/-- The absolute value of an ideal term depends on `s` only through its real part. -/
@[simp]
theorem norm_idealTerm (f : IdealArithmeticFunction K) (s : ℂ) (I : (Ideal (𝓞 K))⁰) :
    ‖idealTerm K f s I‖ = ‖f I‖ / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ s.re := by
  rw [idealTerm_def, norm_div,
    Complex.norm_natCast_cpow_of_pos (Ideal.absNorm_pos_of_nonZeroDivisors I)]









/-! ### Regrouping -/

/-- The `n`-th term of the regrouped `LSeries` is the finite sum of the ideal terms over the
absolute-norm fibre of `n`. -/
theorem term_normCoeff_eq_sum_normFiber (f : IdealArithmeticFunction K) (s : ℂ) (n : ℕ) :
    LSeries.term (normCoeff K f) s n = ∑ I ∈ normFiber K n, idealTerm K f s I := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn, normCoeff_eq_sum_normFiber, Finset.sum_div]
  refine Finset.sum_congr rfl fun I hI ↦ ?_
  rw [idealTerm_def, (mem_normFiber K).mp hI]

/-- The regrouped `LSeries` terms as the fibrewise sums of the ideal terms along the absolute
norm. This is the form consumed by `HasSum.tsum_fiberwise`; `term_normCoeff_eq_sum_normFiber` is
the usable finite-fibre formula. -/
private theorem term_normCoeff (f : IdealArithmeticFunction K) (s : ℂ) :
    LSeries.term (normCoeff K f) s = fun n ↦
      ∑' I : (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) ⁻¹' {n},
        idealTerm K f s I := by
  funext n
  rw [← coe_normFiber, Finset.tsum_subtype' (normFiber K n) (idealTerm K f s)]
  exact term_normCoeff_eq_sum_normFiber K f s n

/-- **Regrouping by absolute norm.** If the Dirichlet series indexed by the nonzero integral ideals
converges absolutely at `s` with sum `L`, then the Mathlib `LSeries` of the regrouped coefficients
`TauCeti.normCoeff f` converges absolutely at `s` with the same sum.

Absolute convergence of the ideal-indexed series is the hypothesis `HasSum`, which for a
complex-valued family is unconditional. No hypothesis on the individual ideal summands is needed;
compare `TauCeti.summable_idealTerm_of_nonneg` for the converse, which does need one. -/
theorem regroupByNorm {f : IdealArithmeticFunction K} {s L : ℂ} (h : HasSum (idealTerm K f s) L) :
    LSeriesHasSum (normCoeff K f) s L := by
  simpa only [LSeriesHasSum, term_normCoeff] using
    h.tsum_fiberwise fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))

/-- Absolute convergence of the ideal-indexed Dirichlet series implies that of the regrouped
`LSeries`. -/
theorem LSeriesSummable_normCoeff {f : IdealArithmeticFunction K} {s : ℂ}
    (h : Summable (idealTerm K f s)) : LSeriesSummable (normCoeff K f) s :=
  LSeriesHasSum.LSeriesSummable (regroupByNorm K h.hasSum)



/-! ### The ideal-indexed abscissa of absolute convergence -/













/-! ### The converse, in the absence of cancellation inside norm fibres -/







/-- **The converse regrouping, under nonnegativity of every ideal summand.** If every value of `f`
is a nonnegative real number, then absolute convergence of the regrouped `LSeries` implies absolute
convergence of the ideal-indexed series.

This is the special case of `TauCeti.summable_idealTerm_of_norm_normCoeff_eq_sum_norm` in which
nonnegativity rules out cancellation. Nonnegativity of the *grouped* coefficients
`TauCeti.normCoeff f` does not suffice; see
`TauCeti.exists_forall_normCoeff_nonneg_not_forall_nonneg`. -/
theorem summable_idealTerm_of_nonneg (f : IdealArithmeticFunction K) (hf : ∀ I, 0 ≤ f I) {s : ℂ}
    (h : LSeriesSummable (normCoeff K f) s) : Summable (idealTerm K f s) :=
  summable_idealTerm_of_norm_normCoeff_eq_sum_norm K f
    (norm_normCoeff_eq_sum_norm_of_nonneg K f hf) h



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
# Linear ideal counts and the exact abscissa of the trivial ideal weight

Mathlib's `NumberField.Ideal.tendsto_norm_le_div_atTop₀` says that the number of nonzero integral
ideals of `𝓞 K` of absolute norm at most `x` is asymptotic to `ρ x`, with `ρ` the positive residue
of the Dedekind zeta function.  This file turns that single asymptotic into the *two-sided* linear
bounds that every later estimate of the roadmap counts against, and then spends them on the exact
abscissa of absolute convergence of the trivial ideal weight.

Both directions are needed.  Convergence uses the upper bound alone: it makes the partial sums of
the norm coefficients `O(n)`, so Mathlib's `LSeriesSummable_of_sum_norm_bigO` gives absolute
convergence on `Re s > 1`.  Divergence at `s = 1` uses both bounds together, to estimate the mass
of a block `N < n ≤ m N` of fixed ratio `m` as a difference of endpoint counts: the lower bound at
the right endpoint `m N` and the upper bound at the left endpoint `N` leave the block at least
`lower * m N - upper * N` of coefficient mass, so the terms `‖a n‖ / n` add up to at least
`lower - upper / m`, which is at least `lower / 2` once `m ≥ 2 * upper / lower`, while the blocks
of a convergent series of nonnegative terms must become arbitrarily small.

## Main definitions

* `TauCeti.IdealCountingLinearBounds K` packages positive constants `lower` and `upper` with the
  two-sided bound `lower * x ≤ #{I ≠ 0 | N(I) ≤ x} ≤ upper * x`, valid from cutoff `1` on.
* `TauCeti.card_primePowersLE_isBigO` transfers the upper ideal-count bound to the number of
  prime-power ideals at most `x`.

## Main results

* `TauCeti.idealCount_linearBounds`: such a package exists for every number field.
* `TauCeti.abscissaOfAbsConv_normCoeff_one`: the abscissa of absolute convergence of the trivial
  ideal weight is exactly `1`; `TauCeti.LSeriesSummable_normCoeff_one_iff` is the sharp
  convergence criterion.
* `TauCeti.abscissaOfAbsConv_dedekindZetaCoeff` and `TauCeti.LSeriesSummable_dedekindZetaCoeff_iff`
  are the same two statements for `TauCeti.dedekindZetaCoeff`, the coefficient system Mathlib's
  `NumberField.dedekindZeta` is the `LSeries` of.  That system counts *all* integral ideals, so it
  differs from the trivial norm coefficients at `n = 0` and the two statements are related only
  through the `n ≠ 0` congruence `LSeries.abscissaOfAbsConv_congr`.
* `TauCeti.summable_idealTerm_of_bounded_of_one_lt_re`: a uniformly bounded weight has an
  absolutely convergent ideal-indexed Dirichlet series on `Re s > 1`, and
  `TauCeti.summable_idealTerm_of_unitary_of_one_lt_re` is its unitary specialization.
* `TauCeti.idealAbscissaOfAbsConv_lt_re_of_bounded`: the same hypothesis places the ideal-indexed
  abscissa of absolute convergence strictly below every `Re s > 1`.

## Implementation notes

The counting function is Mathlib's own
`Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x}`, written out rather
than abbreviated, so that the bounds apply to `NumberField.Ideal.tendsto_norm_le_div_atTop₀`
without a translation lemma.  The inclusive real cutoff is the one fixed by the conventions table
of the roadmap.

`TauCeti.NumberTheory.EffectiveBounds.IdealCount` proves the *effective* bound
`#{I ≠ 0 | N(I) ≤ x} ≤ x² 2^[K:ℚ]`, with an explicit constant but the wrong exponent; it cannot
prove convergence at `Re s > 1`, and it has no lower bound at all.

## Relationship to other estimates

The unweighted prime-power cardinality estimate is separate from the weighted higher-prime-power
estimates in `HigherPrimePowers.lean`.  The abscissa results above depend only on the two-sided
linear ideal counts, not on the analytic continuation of the Dedekind zeta function or its pole at
`s = 1`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters II--III.
-/

 section

namespace TauCeti

open _root_.Filter
open scoped _root_.nonZeroDivisors _root_.NumberField _root_.Topology _root_.ComplexOrder

variable (K : Type*) [Field K] [NumberField K]

/-! ### Finiteness and monotonicity of the ideal count -/







/-! ### Two-sided linear bounds -/











/-! ### Partial sums of the trivial norm coefficients -/







/-! ### The exact abscissa of the trivial ideal weight -/















/-! ### The exact abscissa, and its Dedekind zeta form -/





/-- The ideal-indexed Dirichlet series of the trivial ideal weight converges absolutely exactly on
`Re s > 1`. -/
theorem summable_idealTerm_one_iff {K : Type*} [Field K] [NumberField K] {s : ℂ} :
    Summable (idealTerm K (1 : IdealArithmeticFunction K) s) ↔ 1 < s.re := by
  refine ⟨fun h ↦ (LSeriesSummable_normCoeff_one_iff K).mp (LSeriesSummable_normCoeff K h),
    fun h ↦ ?_⟩
  exact summable_idealTerm_of_nonneg K 1 (fun _ ↦ zero_le_one)
    ((LSeriesSummable_normCoeff_one_iff K).mpr h)

/-- **A uniformly bounded weight converges wherever the trivial weight does.** If every value of
`f` on a nonzero integral ideal has modulus at most `C`, its ideal-indexed Dirichlet series
converges absolutely on `Re s > 1`.

The bound may be any nonnegative real — a negative `C` makes the hypothesis unsatisfiable, since
`‖f I‖` is a norm — and no `C = 1` normalisation is wanted, since a weight is often bounded by
something other than `1` without being rescaled. The unitary case — a Dirichlet or Galois
character, of modulus `1` at the good primes and `0` at the bad ones — is `C = 1`, and is packaged
as `summable_idealTerm_of_unitary_of_one_lt_re`. Stating the hypothesis here as a bound rather than
as unitarity is what lets the vanishing at the bad primes pass without a special case.

Only one direction holds, unlike `summable_idealTerm_one_iff`: a weight that vanishes identically
is bounded by every nonnegative `C` and converges everywhere. -/
theorem summable_idealTerm_of_bounded_of_one_lt_re {K : Type*} [Field K] [NumberField K]
    {f : IdealArithmeticFunction K} {C : ℝ} (hf : ∀ I : (Ideal (𝓞 K))⁰, ‖f I‖ ≤ C) {s : ℂ}
    (hs : 1 < s.re) : Summable (idealTerm K f s) := by
  refine Summable.of_norm_bounded
    (g := fun I ↦ C * ‖idealTerm K (1 : IdealArithmeticFunction K) s I‖)
    (((summable_idealTerm_one_iff.mpr hs).norm).mul_left C) fun I ↦ ?_
  rw [norm_idealTerm, norm_idealTerm]
  have hpos : (0 : ℝ) < (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ s.re :=
    Real.rpow_pos_of_pos (by exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I) _
  have hone : ‖(1 : IdealArithmeticFunction K) I‖ = 1 := by simp
  rw [hone, mul_one_div]
  gcongr
  exact hf I

/-- **A unitary weight converges on `Re s > 1`.** The specialization of
`summable_idealTerm_of_bounded_of_one_lt_re` at `C = 1`, through
`TauCeti.UnitaryIdealWeight.norm_le_one`: a unitary weight has modulus `1` on the good ideals and
vanishes on the rest, so it is bounded by `1` on all of them and the caller is left no case split.

This is the form the Euler-product code consumes, its `hasProd_eulerFactor` asking for exactly a
`Summable (idealTerm K · s)` hypothesis on the weight's passage to `IdealArithmeticFunction`. -/
theorem summable_idealTerm_of_unitary_of_one_lt_re {K : Type*} [Field K] [NumberField K]
    (χ : UnitaryIdealWeight K) {s : ℂ} (hs : 1 < s.re) :
    Summable (idealTerm K χ.toIdealArithmeticFunction s) := by
  refine summable_idealTerm_of_bounded_of_one_lt_re (C := 1) (fun I ↦ ?_) hs
  rw [UnitaryIdealWeight.toIdealArithmeticFunction_apply]
  exact χ.norm_le_one _







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
# Canonical local factors and formal Euler products for ideal arithmetic functions

This file develops the Euler-product layer for arithmetic functions on nonzero ideals. It builds
the canonical formal power series at each height-one prime and sends that series into Mathlib's
`ArithmeticFunction.ofPowerSeries` API. The resulting local arithmetic factor has the prescribed
prime-power values and vanishes away from powers of the prime-ideal norm.

It then restricts an ideal arithmetic function to the nonzero ideals whose prime factors lie in a
prescribed set of height-one primes, and proves that for a *finite* set of primes the norm
coefficients of that restriction are exactly the product of the local factors, taken in Mathlib's
Dirichlet convolution of arithmetic functions. Passing to Mathlib's formal Euler product gives the
norm coefficients of the original function. Everything here is a formal identity of coefficients:
no analytic convergence hypothesis enters.

## Main definitions

* `TauCeti.IdealArithmeticFunction.localPowerSeries` has coefficient `f (P ^ n)` at `n`.
* `TauCeti.IdealArithmeticFunction.localArithmeticFactor` realizes that power series as an
  arithmetic function supported on powers of `N(P)`.
* `TauCeti.IdealArithmeticFunction.supportedPart f S` is `f` restricted to the nonzero ideals all
  of whose prime factors lie in `S`, and zero elsewhere.

## Main results

* `TauCeti.IdealArithmeticFunction.supportedPart_insert`: for a multiplicative `f`, adjoining one
  prime to the support convolves the restriction with the restriction to the powers of that prime.
* `TauCeti.IdealArithmeticFunction.normCoeff_supportedPart`: the **finite Euler product**
  `normCoeff (supportedPart f S) = ∏ P ∈ S, localArithmeticFactor f P` for a multiplicative `f`
  and a finite set `S` of height-one primes.
* `TauCeti.IdealArithmeticFunction.normCoeff_eq_eulerProduct`: the norm coefficients of a
  multiplicative ideal arithmetic function are Mathlib's formal Euler product of its canonical
  local factors.

## Implementation notes

"Supported on `S`" is spelled `Ideal.IsPrimeTo · Sᶜ`: no prime *outside* `S` divides the ideal.
That predicate, and the splitting `Ideal.IsPrimeTo.exists_eq_pow_mul` of an ideal into a prime
power times a cofactor together with its uniqueness `Ideal.eq_and_eq_of_pow_mul_eq_pow_mul`, live
in `TauCeti/RingTheory/DedekindDomain/Ideal.lean`, since nothing in them is specific to a number
field. Uniqueness is what makes the induction work: it is why exactly one summand of the ideal
convolution survives at each ideal. The multiplicativity of `f` over a prime-power factorization,
`TauCeti.IdealArithmeticFunction.IsMultiplicative.map_prod_pow`, likewise lives with the predicate
it elaborates, in `TauCeti/NumberTheory/ArithmeticDirichletSeries/Basic.lean`.

`TauCeti.MultiplicativeIdealWeight.restrict` is the opposite regime and is not a substitute:
it restricts *away from* a **finite** set of primes and stays inside the bundled weight carrier. A
finite Euler product needs support on a *finite* set of primes, so all but finitely many primes are
bad; such a function is never a `MultiplicativeIdealWeight`, whose zero support is finite by
definition. Hence `supportedPart` is a plain ideal arithmetic function.

Finiteness is what carries the finite products to the full Euler product. A nonzero ideal has
only finitely many prime divisors, and only finitely many primes have norm at most a given `n`, so
at a fixed norm coefficient the restriction `supportedPart f S` already agrees with `f` as soon as
`S` contains those primes. Each finite product is therefore eventually the exact norm coefficient,
and Mathlib's `ArithmeticFunction.eulerProduct`, being the limit of those finite products, computes
the norm coefficients of `f` itself. The local factors are derived from `f` rather than stored, so
this identity holds for any multiplicative `f` with no further data.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* Mathlib's `ArithmeticFunction.ofPowerSeries` and `ArithmeticFunction.eulerProduct` APIs.
* `TauCetiRoadmap/ArithmeticDirichletSeries/Suggested.lean`, whose local-factor target signatures
  and naming are adapted here.
-/

 section

open scoped _root_.nonZeroDivisors _root_.NumberField
open _root_.IsDedekindDomain (HeightOneSpectrum)

namespace IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K]



/-- A prime power, as a nonzero integral ideal, has the expected underlying ideal. -/
@[simp]
theorem coe_primeIdealPow (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) :
    (primeIdealPow P e : Ideal (𝓞 K)) = P.asIdeal ^ e :=
  (rfl)

variable [NumberField K]

/-- The absolute norm is multiplicative on prime powers. -/
theorem absNorm_primeIdealPow (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) :
    Ideal.absNorm (primeIdealPow P e : Ideal (𝓞 K)) = Ideal.absNorm P.asIdeal ^ e := by
  rw [coe_primeIdealPow, map_pow]

omit [NumberField K] in
/-- Distinct primes give distinct first powers, so a family indexed by the primes is a subfamily
of one indexed by the nonzero ideals. -/
theorem primeIdealPow_one_injective :
    Function.Injective fun P : HeightOneSpectrum (𝓞 K) ↦ primeIdealPow P 1 := fun P Q h ↦
  HeightOneSpectrum.asIdeal_injective
    (by simpa only [coe_primeIdealPow, pow_one] using
      congrArg (Subtype.val : (Ideal (𝓞 K))⁰ → Ideal (𝓞 K)) h)

/-- Distinct exponents give distinct prime powers. -/
theorem primeIdealPow_injective (P : HeightOneSpectrum (𝓞 K)) :
    Function.Injective (primeIdealPow P) := fun m n h ↦
  Nat.pow_right_injective (NumberField.HeightOneSpectrum.one_lt_absNorm P)
    (by simpa only [absNorm_primeIdealPow] using
      congrArg (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) h)

end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti



namespace IdealArithmeticFunction

variable {K : Type*} [Field K]

variable [NumberField K]



























/-! ### Finite Euler products -/



variable {f : IdealArithmeticFunction K} {S : Set (HeightOneSpectrum (𝓞 K))}
  {A : (Ideal (𝓞 K))⁰}































end IdealArithmeticFunction

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
# Euler-product coefficient data over a number field

This file bundles the algebraic input for an Euler product over the height-one primes of the ring
of integers of a number field. An `EulerProductData K` consists of an ideal arithmetic function
that is multiplicative on relatively prime nonzero ideals. The prime-power series and local
arithmetic factors are canonically derived from the function as defined in
`EulerProduct/Basic.lean`, so nothing about the local behaviour is stored: the bundle carries
exactly the one algebraic hypothesis that an Euler product consumes.

The formal Euler-product identity follows from
`IdealArithmeticFunction.normCoeff_eq_eulerProduct`: coprime multiplicativity and unique
factorization prove that `normCoeff` is Mathlib's `ArithmeticFunction.eulerProduct` of the
canonical local factors.

Two hypotheses of the classical theory are deliberately absent, because the identity proved here
does not need either. There is no distinguished finite set of exceptional primes: multiplicativity
is required on every coprime pair of nonzero ideals, and the local factor at a prime is read off
from the coefficients at its powers, good or bad. There is also no analytic input: the identity is
an equality of arithmetic functions, and the convergence of the evaluated factors to an infinite
product is a separate question.

## Main definitions

* `TauCeti.EulerProductData` bundles a multiplicative ideal coefficient system.
* `TauCeti.EulerProductData.ofMultiplicativeIdealWeight` regards a degree-one ideal weight as
  Euler-product data.
* Pointwise multiplication, complex conjugation, and restriction away from sets of primes
  preserve the bundle.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* Mathlib's `ArithmeticFunction.ofPowerSeries` and `ArithmeticFunction.eulerProduct` APIs.
-/

 section

namespace TauCeti

open scoped _root_.nonZeroDivisors _root_.NumberField
open _root_.IsDedekindDomain (HeightOneSpectrum)



namespace EulerProductData

variable {K : Type*} [Field K] [NumberField K]



























/-- The coefficient function underlying the Euler-product data of a multiplicative ideal weight. -/
@[simp]
theorem toIdealArithmeticFunction_ofMultiplicativeIdealWeight (χ : MultiplicativeIdealWeight K) :
    (ofMultiplicativeIdealWeight χ).toIdealArithmeticFunction = χ.toIdealArithmeticFunction := by
  funext I
  rfl





















end EulerProductData

end TauCeti

end
end

section
set_option autoImplicit true
namespace TauCeti.IdealArithmeticFunction
end TauCeti.IdealArithmeticFunction
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The analytic Euler product of an ideal arithmetic function

`TauCeti.EulerProductData.normCoeff_eq_eulerProduct` identifies the norm coefficients of bundled
Euler-product data with a formal Euler product, coefficient by coefficient. This file supplies the
analytic statement it does not: where the Dirichlet series indexed by the nonzero ideals converges
absolutely, the infinite product of the local Euler factors converges, in the unrestricted sense
of `HasProd` over the height-one primes, to the `LSeries` of the norm coefficients.

The local factor at a height-one prime `P` is the `LSeries` of the canonical local arithmetic
factor, equivalently the prime-power Dirichlet series `∑' e, f (P ^ e) / N(P ^ e) ^ s`. For a
completely multiplicative weight that series is geometric, and the factor takes the familiar
closed form `(1 - χ(P) N(P) ^ (-s))⁻¹`; specializing to the trivial weight gives the Euler
product of the Dedekind zeta function.

## Main definitions

* `TauCeti.EulerProductData.eulerFactor`: the local Euler factor at a height-one prime.

## Main results

* `TauCeti.EulerProductData.hasProd_eulerFactor`: the **analytic Euler product**, when the
  ideal-indexed Dirichlet series converges absolutely at `s`.
* `TauCeti.EulerProductData.norm_absNorm_cpow_neg_le_radius_localPowerSeries`: a lower bound for
  the convergence radius of a local power series from absolute convergence at a real point.
* `TauCeti.MultiplicativeIdealWeight.hasProd_eulerFactor`: the same product, with the local factors
  in the closed geometric form available for a completely multiplicative weight.
* `TauCeti.MultiplicativeIdealWeight.LSeries_ne_zero_of_summable_idealTerm`: the `L`-series is
  **nonzero** wherever the ideal-indexed series converges absolutely.
* `TauCeti.dedekindZeta_eulerProduct_hasProd`: the **Euler product of the Dedekind zeta
  function**, valid on `Re s > 1`.
* `TauCeti.dedekindZeta_ne_zero_of_one_lt_re`: the Dedekind zeta function is **nonzero** on
  `Re s > 1`.
* `IsDedekindDomain.HeightOneSpectrum.one_lt_norm_absNorm_cpow` and
  `IsDedekindDomain.HeightOneSpectrum.absNorm_cpow_sub_one_ne_zero`: analytic bounds for the
  complex powers of prime-ideal norms on the right half-plane.
* `IsDedekindDomain.HeightOneSpectrum.logDeriv_one_sub_absNorm_cpow_neg`: the logarithmic
  derivative of a deleted Euler factor.

The nonvanishing is pointwise, at each `s` where the ideal-indexed series converges absolutely, and
nothing is claimed off that region. It is not a formality: an unconditionally convergent product of
nonzero factors may still vanish.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* Mathlib's `EulerProduct` API, whose `Nat.Primes`-indexed statements this file mirrors for the
  height-one primes of a number field.
-/

 section

open scoped _root_.NumberField
open _root_.IsDedekindDomain (HeightOneSpectrum)

namespace IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K]











end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti

open scoped _root_.nonZeroDivisors _root_.ComplexOrder

variable {K : Type*} [Field K] [NumberField K]

namespace EulerProductData

open _root_.TauCeti.IdealArithmeticFunction

variable (D : EulerProductData K) {s : ℂ}

/-! ### The local Euler factor -/







end EulerProductData

namespace IdealArithmeticFunction

variable {f : IdealArithmeticFunction K} {s : ℂ}

/-! ### Restriction to a set of primes, analytically -/













/-- **The prime terms are a subseries of the ideal terms.** Each height-one prime contributes its
own ideal as the `e = 1` member of its power series, and distinct primes give distinct ideals, so
absolute convergence over ideals restricts to the primes. Multiplicativity plays no part. -/
theorem summable_idealTerm_primeIdealPow_one (hs : Summable (idealTerm K f s)) :
    Summable fun P : HeightOneSpectrum (𝓞 K) ↦ idealTerm K f s (P.primeIdealPow 1) :=
  hs.comp_injective HeightOneSpectrum.primeIdealPow_one_injective

end IdealArithmeticFunction

namespace EulerProductData

open _root_.TauCeti.IdealArithmeticFunction

variable (D : EulerProductData K) {s : ℂ}













/-! ### The infinite Euler product -/







end EulerProductData

/-! ### Completely multiplicative weights -/

namespace MultiplicativeIdealWeight

open _root_.TauCeti.IdealArithmeticFunction

variable (χ : MultiplicativeIdealWeight K) {s : ℂ}

/-- The ideal terms of a completely multiplicative weight along the powers of a prime form a
geometric progression. -/
@[simp]
theorem idealTerm_toIdealArithmeticFunction_primeIdealPow (P : HeightOneSpectrum (𝓞 K)) (e : ℕ)
    (s : ℂ) :
    idealTerm K χ.toIdealArithmeticFunction s (P.primeIdealPow e) =
      (χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s) ^ e := by
  rw [idealTerm_def, toIdealArithmeticFunction_apply,
    P.absNorm_primeIdealPow, P.coe_primeIdealPow,
    map_pow, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul,
    Complex.cpow_nat_mul, div_pow]

/-- **The local ratio of a convergent weight is a contraction.** Absolute convergence of the
ideal-indexed Dirichlet series forces the geometric ratio at each prime to have modulus less than
one, because the powers of that prime already contribute a geometric subseries. -/
theorem norm_div_lt_one_of_summable_idealTerm
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s))
    (P : HeightOneSpectrum (𝓞 K)) :
    ‖χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s‖ < 1 := by
  rw [← summable_geometric_iff_norm_lt_one]
  exact (hs.comp_injective P.primeIdealPow_injective).congr fun e ↦
    idealTerm_toIdealArithmeticFunction_primeIdealPow χ P e s

/-- **The local ratios are summable over the primes.** The multiplicative specialisation of
`IdealArithmeticFunction.summable_idealTerm_primeIdealPow_one`: at a prime the ideal term *is* the
ratio `χ(P) N(P)⁻ˢ`. -/
theorem summable_div_of_summable_idealTerm
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    Summable fun P : HeightOneSpectrum (𝓞 K) ↦
      χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s :=
  (IdealArithmeticFunction.summable_idealTerm_primeIdealPow_one hs).congr fun P ↦ by
    simp [idealTerm_toIdealArithmeticFunction_primeIdealPow χ P 1 s]

/-- Absolute convergence puts every local ratio `χ(P) N(P)⁻ˢ` strictly inside the unit disc, so no
local Euler factor has a vanishing denominator. -/
theorem one_sub_div_ne_zero_of_summable_idealTerm
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) (P : HeightOneSpectrum (𝓞 K)) :
    1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s ≠ 0 := fun h ↦ by
  have hlt := norm_div_lt_one_of_summable_idealTerm χ hs P
  rw [sub_eq_zero] at h
  rw [← h] at hlt
  simp at hlt

/-- The local Euler factor of a completely multiplicative weight is the geometric closed form
`(1 - χ(P) N(P)⁻ˢ)⁻¹`. -/
theorem eulerFactor_ofMultiplicativeIdealWeight
    (P : HeightOneSpectrum (𝓞 K))
    (hP : ‖χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s‖ < 1) :
    (EulerProductData.ofMultiplicativeIdealWeight χ).eulerFactor P s =
      (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)⁻¹ := by
  rw [EulerProductData.eulerFactor_eq_tsum,
    EulerProductData.toIdealArithmeticFunction_ofMultiplicativeIdealWeight,
    tsum_congr fun e ↦ idealTerm_toIdealArithmeticFunction_primeIdealPow χ P e s]
  exact tsum_geometric_of_norm_lt_one hP

/-- **The Euler product of a completely multiplicative ideal weight.** -/
theorem hasProd_eulerFactor (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    HasProd (fun P : HeightOneSpectrum (𝓞 K) ↦
        (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)⁻¹)
      (LSeries (normCoeff K χ.toIdealArithmeticFunction) s) := by
  have hfun : (fun P : HeightOneSpectrum (𝓞 K) ↦
      (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)⁻¹) =
      fun P ↦ (EulerProductData.ofMultiplicativeIdealWeight χ).eulerFactor P s :=
    funext fun P ↦ (eulerFactor_ofMultiplicativeIdealWeight χ P
      (norm_div_lt_one_of_summable_idealTerm χ hs P)).symm
  rw [hfun]
  have hprod := (EulerProductData.ofMultiplicativeIdealWeight χ).hasProd_eulerFactor
    (s := s) (by
      simpa only [EulerProductData.toIdealArithmeticFunction_ofMultiplicativeIdealWeight] using hs)
  simpa only [EulerProductData.toIdealArithmeticFunction_ofMultiplicativeIdealWeight] using hprod



end MultiplicativeIdealWeight

/-! ### The Dedekind zeta function -/







end TauCeti

end
end

section
set_option autoImplicit true
namespace TauCeti.IdealArithmeticFunction
end TauCeti.IdealArithmeticFunction
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The Euler product over the primes of a number field, in exponential form

Mathlib's `EulerProduct.exp_tsum_primes_log_eq_tsum` writes the Euler product of a completely
multiplicative `f : ℕ →*₀ ℂ` as `exp (∑' p, -log (1 - f p))`. This file is the ideal-indexed
analogue, over the height-one primes of the ring of integers of a number field, mirroring the way
`TauCeti.MultiplicativeIdealWeight.hasProd_eulerFactor` mirrors Mathlib's product form.

The logarithm is taken factor by factor, using the principal value: absolute convergence of the
ideal-indexed series forces each local ratio into the open unit disc, where `Complex.log (1 - ·)`
is defined without choosing anything.

**What this does not give.** `exp` is not injective, so an identity of the form `exp t = L`
determines `t` only modulo `2πi ℤ`; these theorems therefore do not exhibit a logarithm *of* the
`L`-series, and in particular are not a holomorphic branch on a region.
`TauCeti.MultiplicativeIdealWeight.LSeries_ne_zero_of_summable_idealTerm` supplies nonvanishing
pointwise, wherever the ideal-indexed series converges absolutely; a branch needs more than that —
a simply connected zero-free region on which to choose one — and is not constructed here.

## Main results

* `TauCeti.MultiplicativeIdealWeight.summable_neg_log_one_sub`: summability of the
  prime-indexed logarithm sum wherever the ideal-indexed series converges absolutely.
* `TauCeti.MultiplicativeIdealWeight.exp_tsum_neg_log_one_sub_eq_LSeries`: the `L`-series as the
  exponential of a sum of principal logarithms over the primes.
* `TauCeti.MultiplicativeIdealWeight.tsum_prime_pow_eq_tsum_neg_log_one_sub`: that sum re-indexed
  by a prime and an exponent, as an identity of complex numbers.
* `TauCeti.MultiplicativeIdealWeight.exp_tsum_prime_pow_eq_LSeries`: the exponential form of the
  re-indexed sum.
-/

 section

namespace TauCeti

open _root_.Complex _root_.IsDedekindDomain

open scoped _root_.NumberField

namespace MultiplicativeIdealWeight

open _root_.TauCeti.IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K] (χ : MultiplicativeIdealWeight K) {s : ℂ}

/-- The prime-indexed sum of principal logarithms converges whenever the ideal-indexed series
of a multiplicative ideal weight converges absolutely. -/
theorem summable_neg_log_one_sub
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    Summable (fun P : HeightOneSpectrum (𝓞 K) ↦
      -log (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)) :=
  (Summable.clog_one_sub (χ.summable_div_of_summable_idealTerm hs)).neg

/-- **The Euler product in exponential form.** For a completely multiplicative ideal weight whose
ideal-indexed series converges absolutely at `s`, the `L`-series is the exponential of the sum of
principal logarithms `-log (1 - χ(P) N(P)⁻ˢ)` over the height-one primes.

The sum is not thereby a logarithm of the `L`-series: `exp` identifies it only modulo `2πi ℤ`.
This is the number-field analogue of Mathlib's `EulerProduct.exp_tsum_primes_log_eq_tsum`, and
carries the same limitation. -/
theorem exp_tsum_neg_log_one_sub_eq_LSeries
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    exp (∑' P : HeightOneSpectrum (𝓞 K),
        -log (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)) =
      LSeries (normCoeff K χ.toIdealArithmeticFunction) s := by
  have hne := χ.one_sub_div_ne_zero_of_summable_idealTerm hs
  have H := (χ.summable_neg_log_one_sub hs).hasSum.cexp.tprod_eq
  simp only [Function.comp_apply, exp_neg, exp_log (hne _)] at H
  exact H.symm.trans (χ.hasProd_eulerFactor hs).tprod_eq





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
# The 3-4-1 positivity combination

This file packages the elementary positivity input in the classical `3-4-1` argument for
nonvanishing of Dirichlet series. For a phase `z` on the complex unit circle,

```text
3 + 4 Re(z) + Re(z²) = 2 (1 + Re(z))² ≥ 0.
```

The weights `3`, `4`, and `1` are nonnegative. We record their expression as a finite nonnegative
trigonometric combination and prove the corresponding inequality for logarithms of Euler factors.
These results contain no continuation, nonvanishing, or character-specific hypotheses; downstream
applications provide those analytic inputs separately.

## Main declarations

* `TauCeti.LSeries.isNonnegativeTrigonometricCombination_threeFourOne` packages the frequencies
  `0`, `1`, and `2` with weights `3`, `4`, and `1`.
* `TauCeti.LSeries.threeFourOne_re_neg_log_one_sub_nonneg` is the corresponding inequality for
  logarithms of Euler factors in the open unit disk.

## Provenance

The `3-4-1` argument is classical; see Davenport, *Multiplicative Number Theory*, Chapter 4.
The logarithmic form specializes the private lemma `DirichletCharacter.re_log_comb_nonneg'` in
Mathlib's `Mathlib/NumberTheory/LSeries/Nonvanishing.lean`, by Michael Stoll and David Loeffler,
through `TauCeti.sum_re_neg_log_one_sub_nonneg`.
-/

 section

namespace TauCeti.LSeries

open Complex

noncomputable section

/-! ### The concrete 3-4-1 combination -/







/-- The first `3-4-1` weight is `3`. -/
@[simp] theorem threeFourOneWeight_zero : threeFourOneWeight 0 = 3 := (rfl)

/-- The second `3-4-1` weight is `4`. -/
@[simp] theorem threeFourOneWeight_one : threeFourOneWeight 1 = 4 := (rfl)

/-- The third `3-4-1` weight is `1`. -/
@[simp] theorem threeFourOneWeight_two : threeFourOneWeight 2 = 1 := (rfl)

/-- The first `3-4-1` frequency is `0`. -/
@[simp] theorem threeFourOneFrequency_zero : threeFourOneFrequency 0 = 0 := (rfl)

/-- The second `3-4-1` frequency is `1`. -/
@[simp] theorem threeFourOneFrequency_one : threeFourOneFrequency 1 = 1 := (rfl)

/-- The third `3-4-1` frequency is `2`. -/
@[simp] theorem threeFourOneFrequency_two : threeFourOneFrequency 2 = 2 := (rfl)

/-- The defining formula for `threeFourOneCombination`. -/
theorem threeFourOneCombination_def (z : ℂ) :
    threeFourOneCombination z = 3 + 4 * z.re + (z ^ 2).re := (rfl)

/-- The abstract finite combination with `3-4-1` weights is the usual concrete expression. -/
@[simp]
theorem trigonometricCombination_threeFourOne (z : ℂ) :
    trigonometricCombination Finset.univ threeFourOneWeight threeFourOneFrequency z =
      threeFourOneCombination z := by
  rw [trigonometricCombination_def, threeFourOneCombination_def, Fin.sum_univ_three]
  simp only [threeFourOneWeight_zero, threeFourOneWeight_one, threeFourOneWeight_two,
    threeFourOneFrequency_zero, threeFourOneFrequency_one, threeFourOneFrequency_two,
    pow_zero, pow_one, one_re, mul_one, one_mul]

/-- On the unit circle the `3-4-1` expression is twice a square. -/
theorem threeFourOneCombination_eq_two_mul_sq {z : ℂ} (hz : ‖z‖ = 1) :
    threeFourOneCombination z = 2 * (z.re + 1) ^ 2 := by
  rw [threeFourOneCombination_def, pow_two, mul_re, ← sq, ← sq,
    ← Complex.sq_norm_sub_sq_re, hz]
  ring

/-- The weights and frequencies of the `3-4-1` expression form a finite nonnegative
trigonometric combination. -/
theorem isNonnegativeTrigonometricCombination_threeFourOne :
    IsNonnegativeTrigonometricCombination Finset.univ threeFourOneWeight
      threeFourOneFrequency := by
  intro z hz
  rw [trigonometricCombination_threeFourOne, threeFourOneCombination_eq_two_mul_sq hz]
  positivity



/-! ### Euler-factor form -/

/-- The `3-4-1` inequality for logarithms of three Euler factors in the open unit disk. -/
theorem threeFourOne_re_neg_log_one_sub_nonneg {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re +
      (-log (1 - a * z ^ 2)).re := by
  have h := sum_re_neg_log_one_sub_nonneg
    isNonnegativeTrigonometricCombination_threeFourOne ha₀ ha₁ hz
  simpa only [trigonometricCombination_def, Fin.sum_univ_three, threeFourOneWeight_zero,
    threeFourOneWeight_one, threeFourOneWeight_two, threeFourOneFrequency_zero,
    threeFourOneFrequency_one, threeFourOneFrequency_two, pow_zero, pow_one, mul_one,
    one_mul] using h

end

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
# The 3-4-1 bound for the Euler products of unitary ideal weights

Let `χ` be a unitary ideal weight of a number field `K`, and let `χ₀` be a weight that is trivial
on its good ideals and whose bad primes are among those of `χ` — for instance the trivial weight,
whose `L`-series is the Dedekind zeta function `ζ_K`. For real `σ > 1` and real `t`, this file
proves the classical `3-4-1` inequality

```text
1 ≤ ‖L(χ₀, σ) ^ 3 * L(χ, σ + it) ^ 4 * L(χ², σ + 2it)‖,
```

where each `L`-series is the `LSeries` of the norm coefficients of the weight. It is the
positivity input for nonvanishing on the line `Re s = 1`, and is exactly the bound hypothesis of
the analytic criterion `TauCeti.LSeries.ne_zero_of_threeFourOne`: a continuation of `L(χ, ·)`
that is differentiable at `1 + it` does not vanish there, provided `L(χ₀, σ) = O((σ - 1)⁻¹)` as
`σ → 1⁺` and `L(χ², ·)` continues continuously to `1 + 2it`.

## Main results

* `TauCeti.UnitaryIdealWeight.norm_LSeries_threeFourOne_ge_one`: the `3-4-1` bound for a unitary
  weight `χ` against a weight `χ₀` trivial on its good ideals, with bad primes among those of `χ`.
* `TauCeti.UnitaryIdealWeight.norm_dedekindZeta_threeFourOne_ge_one`: the case `χ₀ = 1`, where the
  first factor is the Dedekind zeta function.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 4.
* The global argument is that of Mathlib's `DirichletCharacter.norm_LSeries_product_ge_one` in
  `Mathlib/NumberTheory/LSeries/Nonvanishing.lean`, by Michael Stoll and David Loeffler, with
  unitary ideal weights of a number field in place of Dirichlet characters.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open Complex IsDedekindDomain NumberField

variable {K : Type*} [Field K] [NumberField K]

namespace TauCeti.UnitaryIdealWeight
end TauCeti.UnitaryIdealWeight
section UnitaryIdealWeight
open TauCeti TauCeti.UnitaryIdealWeight

variable {χ₀ : MultiplicativeIdealWeight K}

/-- The local `3-4-1` inequality at a single prime. It needs only `σ > 0`, which puts
`N(𝔭) ^ (-σ)` in the open unit interval. -/
private theorem TauCeti.UnitaryIdealWeight.threeFourOne_local_nonneg {χ : _root_.TauCeti.UnitaryIdealWeight K}
    (h₀ : χ₀.IsTrivialOnGood) (hbad : χ₀.badPrimes ⊆ χ.1.badPrimes)
    (P : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    0 ≤ 3 * (-_root_.Complex.log (1 - χ₀ P.asIdeal / (_root_.Ideal.absNorm P.asIdeal : ℂ) ^ (σ : ℂ))).re +
      4 * (-_root_.Complex.log (1 - χ.1 P.asIdeal / (_root_.Ideal.absNorm P.asIdeal : ℂ) ^ ((σ : ℂ) + _root_.Complex.I * t))).re +
      (-_root_.Complex.log (1 - (χ ^ 2).1 P.asIdeal /
        (_root_.Ideal.absNorm P.asIdeal : ℂ) ^ ((σ : ℂ) + 2 * _root_.Complex.I * t))).re := by
  rw [_root_.TauCeti.UnitaryIdealWeight.val_pow, _root_.TauCeti.MultiplicativeIdealWeight.pow_apply _ _root_.two_ne_zero]
  by_cases hP : χ₀ P.asIdeal = 0
  · -- a bad prime of `χ₀` is a bad prime of `χ`, so every Euler factor is `1`
    have hχ : χ.1 P.asIdeal = 0 :=
      MultiplicativeIdealWeight.mem_badPrimes.mp
        (hbad (MultiplicativeIdealWeight.mem_badPrimes.mpr hP))
    simp [hP, hχ]
  · have h1 : χ₀ P.asIdeal = 1 := h₀.apply_eq_one ((χ₀.apply_ne_zero_iff_isGood _).mp hP)
    have hN1 : 1 < _root_.Ideal.absNorm P.asIdeal := _root_.NumberField.HeightOneSpectrum.one_lt_absNorm P
    have hN : (0 : ℝ) < _root_.Ideal.absNorm P.asIdeal := by positivity
    have hNc : (_root_.Ideal.absNorm P.asIdeal : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    set a : ℝ := (_root_.Ideal.absNorm P.asIdeal : ℝ) ^ (-σ) with ha
    set z : ℂ := χ.1 P.asIdeal / (_root_.Ideal.absNorm P.asIdeal : ℂ) ^ (_root_.Complex.I * t) with hz
    have ha1 : a < 1 :=
      _root_.Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hN1) (_root_.neg_lt_zero.2 hσ)
    have hnz : ‖z‖ ≤ 1 := by
      rw [hz, _root_.norm_div, _root_.Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hN)]
      simpa using χ.norm_le_one P.asIdeal
    have hbase : (_root_.Ideal.absNorm P.asIdeal : ℂ) ^ (σ : ℂ) =
        (((_root_.Ideal.absNorm P.asIdeal : ℝ) ^ σ : ℝ) : ℂ) := by
      simpa using (_root_.Complex.ofReal_cpow (_root_.Nat.cast_nonneg (_root_.Ideal.absNorm P.asIdeal)) σ).symm
    have hainv : (a : ℂ) = ((((_root_.Ideal.absNorm P.asIdeal : ℝ) ^ σ : ℝ) : ℂ))⁻¹ := by
      rw [ha, _root_.Real.rpow_neg hN.le, _root_.Complex.ofReal_inv]
    have e₀ : χ₀ P.asIdeal / (_root_.Ideal.absNorm P.asIdeal : ℂ) ^ (σ : ℂ) = a := by
      rw [h1, hbase, hainv, _root_.one_div]
    have e₁ : χ.1 P.asIdeal / (_root_.Ideal.absNorm P.asIdeal : ℂ) ^ ((σ : ℂ) + _root_.Complex.I * t) = a * z := by
      rw [_root_.Complex.cpow_add _ _ hNc, hbase, hainv, hz]
      field_simp
    have e₂ : χ.1 P.asIdeal ^ 2 / (_root_.Ideal.absNorm P.asIdeal : ℂ) ^ ((σ : ℂ) + 2 * _root_.Complex.I * t) =
        a * z ^ 2 := by
      rw [_root_.mul_assoc, _root_.Complex.cpow_add _ _ hNc, _root_.Complex.cpow_ofNat_mul, hbase, hainv, hz]
      field_simp
    rw [e₀, e₁, e₂]
    exact _root_.TauCeti.LSeries.threeFourOne_re_neg_log_one_sub_nonneg (by positivity) ha1 hnz

/-- **The `3-4-1` bound for unitary ideal weights.** Let `χ` be a unitary weight and `χ₀` a
weight that is trivial on its good ideals, with every bad prime of `χ₀` a bad prime of `χ`. For
real `σ > 1` and real `t`, the `L`-series of `χ₀` at `σ` cubed, times that of `χ` at `σ + it` to
the fourth power, times that of `χ²` at `σ + 2it`, has norm at least one. -/
theorem solution (χ : _root_.TauCeti.UnitaryIdealWeight K)
    (h₀ : χ₀.IsTrivialOnGood) (hbad : χ₀.badPrimes ⊆ χ.1.badPrimes) {σ : ℝ} (hσ : 1 < σ)
    (t : ℝ) :
    1 ≤ ‖_root_.LSeries (_root_.TauCeti.normCoeff K χ₀.toIdealArithmeticFunction) σ ^ 3 *
      _root_.LSeries (_root_.TauCeti.normCoeff K χ.toIdealArithmeticFunction) ((σ : ℂ) + _root_.Complex.I * t) ^ 4 *
      _root_.LSeries (_root_.TauCeti.normCoeff K (χ ^ 2).toIdealArithmeticFunction) ((σ : ℂ) + 2 * _root_.Complex.I * t)‖ := by
  -- Express each factor as an exponential of a prime logarithm sum. At a bad prime of `χ₀`
  -- all three local terms vanish; at every other prime the scalar 3-4-1 bound applies.
  have hS₀ := _root_.TauCeti.summable_idealTerm_of_bounded_of_one_lt_re
    (f := χ₀.toIdealArithmeticFunction) (C := 1) (s := (σ : ℂ))
    (fun I ↦ (χ₀.toIdealArithmeticFunction_apply I).symm ▸ h₀.norm_apply_le_one) (by simpa using hσ)
  have hS₁ : _root_.Summable (_root_.TauCeti.idealTerm K χ.1.toIdealArithmeticFunction ((σ : ℂ) + _root_.Complex.I * t)) := by
    simpa only [_root_.TauCeti.UnitaryIdealWeight.toIdealArithmeticFunction_eq_val] using
      _root_.TauCeti.summable_idealTerm_of_unitary_of_one_lt_re χ (s := (σ : ℂ) + _root_.Complex.I * t)
        (by simpa using hσ)
  have hS₂ : _root_.Summable (_root_.TauCeti.idealTerm K (χ ^ 2).1.toIdealArithmeticFunction
      ((σ : ℂ) + 2 * _root_.Complex.I * t)) := by
    rw [← (χ ^ 2).toIdealArithmeticFunction_eq_val]
    exact _root_.TauCeti.summable_idealTerm_of_unitary_of_one_lt_re (χ ^ 2)
      (s := (σ : ℂ) + 2 * _root_.Complex.I * t) (by simpa using hσ)
  have hs₀ := χ₀.summable_neg_log_one_sub hS₀
  have hs₁ := χ.1.summable_neg_log_one_sub hS₁
  have hs₂ := (χ ^ 2).1.summable_neg_log_one_sub hS₂
  have hE₀ := χ₀.exp_tsum_neg_log_one_sub_eq_LSeries hS₀
  have hE₁ := χ.1.exp_tsum_neg_log_one_sub_eq_LSeries hS₁
  have hE₂ := (χ ^ 2).1.exp_tsum_neg_log_one_sub_eq_LSeries hS₂
  simp only [_root_.TauCeti.UnitaryIdealWeight.toIdealArithmeticFunction_eq_val]
  rw [← hE₀, ← hE₁, ← hE₂, ← _root_.Complex.exp_nat_mul, ← _root_.Complex.exp_nat_mul, ← _root_.Complex.exp_add, ← _root_.Complex.exp_add, _root_.Complex.norm_exp,
    _root_.Real.one_le_exp_iff]
  have hsum := _root_.Complex.hasSum_re
    (((hs₀.hasSum.mul_left 3).add (hs₁.hasSum.mul_left 4)).add hs₂.hasSum)
  push_cast
  refine hsum.nonneg fun P ↦ ?_
  simpa [_root_.Complex.mul_re] using _root_.TauCeti.UnitaryIdealWeight.threeFourOne_local_nonneg h₀ hbad P (zero_lt_one.trans hσ) t



end UnitaryIdealWeight

end TauCeti

end
end
