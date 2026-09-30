-- Prove2me | solution 1 for TauCeti.hasCancellation_iff_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:31:51.511233+00:00
-- url     : https://prove2.me/submissions/c27271b7-8134-4ee3-8a8c-d5f9496ede29

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Cancellation
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_NormCoeff
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_Order_Northcott_Basic
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Ideal
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.LSeries.Basic
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
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real
import Theorems.Thm_TauCeti_MultiplicativeIdealWeight_apply_ne_zero_iff_isGood
import Theorems.Thm_TauCeti_idealSummatory_eq_sum_range_normFiber

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

























































/-!
### Weights that are norm twists on their good locus
-/

























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







































section Transport

variable {L M : Type*} [Field L] [NumberField L] [Field M] [NumberField M]















/-! Transport preserves the pointwise `CommMonoid` structure of the unitary carrier too. -/











end Transport



@[simp]
theorem toIdealArithmeticFunction_apply (χ : UnitaryIdealWeight K) (I : (Ideal (𝓞 K))⁰) :
    χ.toIdealArithmeticFunction I = χ.1 I := (rfl)













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
# Counting carriers for ideals and prime ideals

Every estimate in the arithmetic-Dirichlet-series roadmap counts objects whose absolute norm does
not exceed a *real* cutoff `x`, and always inclusively: an object of norm exactly `x` is counted.
This file fixes that convention once.

The common core is Mathlib's `Northcott` property: a function `N : ι → ℕ` is Northcott when each
set `{i | N i ≤ B}` is finite.  For such an `N`:

* `TauCeti.normLE N x` is the finite set of indices with `(N i : ℝ) ≤ x`;
* `TauCeti.summatory N w x` is the inclusive sum of a weight `w` over `TauCeti.normLE N x`.

Two instances of this core carry the arithmetic content, `TauCeti.idealsLE` for the nonzero
integral ideals of `𝓞 K` and `TauCeti.primesLE` for the height-one primes, with
`TauCeti.idealSummatory`, `TauCeti.primeSummatory`, and `TauCeti.primePowerSummatory` the associated
summatory functions.  The
weighted prime counts of the roadmap are the two named specializations
`TauCeti.primeTheta`, the logarithmically weighted count, and `TauCeti.primeCount`, the
unweighted one; both are restricted to a set `S` of height-one primes through `Set.indicator`,
so no decidability hypothesis is needed on `S`.

A prime-power ideal is `𝔭 ^ k` for a unique height-one prime `𝔭` and a unique `k ≥ 1`;
`TauCeti.primePowerBase` and `TauCeti.primePowerExponent` name that pair, and
`TauCeti.idealPrimePower_eq_of_base_eq_of_exponent_eq` records that it determines the ideal.  The
exponent is `1` exactly on the primes themselves, which is `TauCeti.primePowerExponent_eq_one_iff`;
`TauCeti.IdealPrimePower.ofPrime` is the resulting inclusion of the prime carrier into the
prime-power carrier, and `TauCeti.primePowerSummatory_eq_primeSummatory` uses it to read a
prime-power sum concentrated on the exponent-one part as a sum over primes.

`TauCeti.idealsLE_filter_dvd` identifies the ideals below a cutoff divisible by a fixed nonzero
ideal `P` with the multiples of `P`, and `TauCeti.idealSummatory_ite_dvd` reads the corresponding
part of a summatory function at the rescaled cutoff `x / N(P)`.

Two lemmas move a summatory function between the three carriers.
`TauCeti.idealSummatory_eq_primePowerSummatory` reads an ideal weight vanishing off the prime
powers as a prime-power weight, and `TauCeti.idealSummatory_eq_sum_range_normFiber` regroups an
ideal summatory function into the partial sum, over `n ≤ ⌊x⌋₊`, of the total mass on the norm
fibre at `n`; `TauCeti.idealSummatory_eq_sum_Icc_normCoeff` writes the same regrouping as a
partial sum of `TauCeti.normCoeff`.  Together they present a sum over prime powers as a partial
sum of an `ArithmeticFunction`, which is the shape a Tauberian theorem consumes.

For `0 ≤ x`, a real cutoff and its floor select the same indices, so
`TauCeti.normLE_eq_normLE_natFloor` and `TauCeti.summatory_eq_summatory_natFloor` convert between
the real and natural conventions. The small-cutoff cases are degenerate for a reason worth
recording: a nonzero ideal has absolute norm at least `1`, and a height-one prime at least `2`, so
`TauCeti.idealsLE_one` isolates the unit ideal and `TauCeti.primesLE_eq_empty_of_lt_two` empties the
prime carrier below `2`.

Modifying a weight on a finite set, or a prime set on a finite symmetric difference, changes a
summatory function by a quantity that is eventually the *constant* total discrepancy; this is
`TauCeti.eventually_summatory_sub_eq` and its two prime specializations. Layer 7 uses these to
show that finite changes do not affect a density. In the same spirit,
`TauCeti.primeTheta_isLittleO_of_finite` records that a finite set of primes contributes an
eventually constant amount to `ϑ_K`, hence `o(x)`: an exceptional set can be discarded from a
counting argument outright, not merely from a density. Its `ψ` companion is
`TauCeti.primePsi_isLittleO_of_finite`.

## Roadmap role

This is Layer **4** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`: the finite cutoff
carriers of 4.1, the generic summatory functions on ideals, primes, and prime powers of 4.2, and the
weighted prime counts `primeTheta` and `primeCount` of 4.3. Layer 5 supplies the actual size
estimates for these counts, and consumes the prime base and exponent of a prime-power ideal to
fibre those estimates over the primes.

## References

* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters I--II.
* H. Davenport, *Multiplicative Number Theory*, Chapters 1 and 7.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

 section

namespace TauCeti

open _root_.Filter
open scoped _root_.nonZeroDivisors _root_.NumberField
open _root_.IsDedekindDomain

/-! ### Ideals and height-one primes of bounded absolute norm -/



variable (K : Type*) [Field K] [NumberField K]













variable {K}







/-! ### The prime base and the exponent of a prime-power ideal -/



























































variable (K)

/-! ### Summatory functions over ideals and over primes -/

































variable {K}

namespace MultiplicativeIdealWeight

variable (χ : MultiplicativeIdealWeight K)



end MultiplicativeIdealWeight

variable (K)





/-- **An ideal summatory function is a partial sum of norm coefficients.** The inclusive sum of
`f` over the nonzero integral ideals of absolute norm at most `x` is `∑_{n=1}^{⌊x⌋₊}` of the norm
coefficients of `f`, in the `Finset.Icc 1` form of Mathlib's `LSeries_eq_mul_integral`. -/
theorem idealSummatory_eq_sum_Icc_normCoeff (f : IdealArithmeticFunction K) (x : ℝ) :
    idealSummatory K f x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, normCoeff K f n := by
  rw [idealSummatory_eq_sum_range_normFiber, Nat.range_succ_eq_Icc_zero,
    ← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le _), Finset.sum_insert (by simp),
    normFiber_zero, Finset.sum_empty, zero_add, zero_add]
  exact Finset.sum_congr rfl fun n _ ↦ (normCoeff_eq_sum_normFiber K f n).symm



/-! ### The weighted prime counts -/





variable {K}
variable {S T : Set (HeightOneSpectrum (𝓞 K))} {x : ℝ}

























































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

/-- The trivial ideal weight has norm coefficient the number of nonzero integral ideals of the
given absolute norm, so its absolute value is that count. -/
theorem norm_normCoeff_one (n : ℕ) :
    ‖normCoeff K (1 : IdealArithmeticFunction K) n‖ = (normFiber K n).card := by
  rw [normCoeff_eq_sum_normFiber]
  simp

/-- The norm coefficients of a unitary weight are bounded in modulus by those of the trivial
weight, which count the ideals of each norm. -/
theorem UnitaryIdealWeight.norm_normCoeff_le_norm_normCoeff_one (χ : UnitaryIdealWeight K) (n : ℕ) :
    ‖normCoeff K χ.toIdealArithmeticFunction n‖ ≤
      ‖normCoeff K (1 : IdealArithmeticFunction K) n‖ := by
  rw [norm_normCoeff_one, normCoeff_eq_sum_normFiber]
  refine (norm_sum_le _ _).trans ?_
  simpa using Finset.sum_le_sum fun I (_ : I ∈ normFiber K n) ↦ χ.norm_le_one (I : Ideal (𝓞 K))



/-! ### The exact abscissa of the trivial ideal weight -/















/-! ### The exact abscissa, and its Dedekind zeta form -/

















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
# Cancellation in ideal partial sums and the continued L-function of a weight

For a unitary ideal weight `χ` of a number field `K` of degree `d = [K : ℚ]`, the partial sums
`∑_{N(I) ≤ x} χ(I)` over the nonzero integral ideals are trivially `O(x)`, by the linear ideal
count. For nontrivial finite-order ray class characters, equidistribution among ray classes gives
the stronger bound `O(x ^ (1 - 1 / d))`. This file names that bound as a hypothesis and extracts
its analytic consequence.

* `TauCeti.HasCancellation χ` is the uniform bound
  `‖∑_{N(I) ≤ x} χ(I)‖ ≤ C * x ^ (1 - 1 / d)` for every real cutoff `x ≥ 1`, with the inclusive
  summatory function `TauCeti.idealSummatory`.
  Equivalently (`TauCeti.hasCancellation_iff_isBigO`), the partial sums are
  `O(x ^ (1 - 1 / d))` as `x → ∞`.
* `TauCeti.continuedLFunctionOfWeight χ` is the partial-summation integral
  `s * ∫_{1}^{∞} (∑_{N(I) ≤ t} χ(I)) t ^ (-(s + 1)) dt`.

It agrees with the norm-regrouped L-series of `χ` on `Re s > 1` for *every* unitary weight
(`TauCeti.continuedLFunctionOfWeight_eq_LSeries`), and under `HasCancellation χ` it is holomorphic
on `Re s > 1 - 1 / d` (`TauCeti.differentiableOn_continuedLFunctionOfWeight`); so it is an analytic
continuation of the L-series of `χ` across the line `Re s = 1`.

Both are stable under deleting finitely many Euler factors, the operation a character family
needs at the bad primes of its modulus. A one-prime recurrence relates the partial sums after
inserting a forbidden prime to two partial sums before the insertion
(`TauCeti.MultiplicativeIdealWeight.idealSummatory_restrict_insert`). Iterating this recurrence
shows that cancellation passes to the restriction (`TauCeti.HasCancellation.restrict`); on
`Re s > 1` the two continued
`L`-functions differ by the entire factor `∏ 𝔭 ∈ S, (1 - χ(𝔭) N(𝔭) ^ (-s))`
(`TauCeti.continuedLFunctionOfWeight_restrict_of_one_lt_re`), and under cancellation that identity
propagates to the whole half-plane `Re s > 1 - 1 / d`
(`TauCeti.continuedLFunctionOfWeight_restrict`).

In number-field degree greater than one, cancellation is also invariant under purely imaginary
norm twists (`TauCeti.hasCancellation_normTwist_iff`). Abel summation supplies this because the
cancellation exponent `1 - 1 / [K : ℚ]` is then positive. The degree-one case is deliberately not
claimed: the defining bound has exponent zero, while the absolute bound for the Abel integral is
logarithmic.

The continued `L`-function itself follows these operations. Conjugating the weight reflects it
in the real axis, `L(conj χ, conj s) = conj (L(χ, s))`, at every `s`
(`TauCeti.continuedLFunctionOfWeight_conj`). An imaginary norm twist by `N(I) ^ (-z)` translates
it by `z`: on `Re s > 1` for every weight
(`TauCeti.continuedLFunctionOfWeight_normTwist_of_one_lt_re`), and on the whole half-plane
`Re s > 1 - 1 / d` when both the weight and its twist have cancellation
(`TauCeti.continuedLFunctionOfWeight_normTwist`).

Cancellation is a hypothesis about the partial sums themselves. It cannot be replaced by
finiteness of the image of `χ` or of a quotient through which it factors: the values of a weight
factoring through a finite quotient of the free group on the prime ideals can be prescribed
arbitrarily prime by prime.

Nor is it automatic, and `TauCeti.not_hasCancellation_of_isNormTwistOnGood` says which weights it
excludes: those agreeing with a norm twist `I ↦ N(I) ^ (u * I)` on the ideals prime to their bad
primes. The `L`-series of such a weight is the Dedekind zeta function with finitely many Euler
factors deleted, read at `s - u * I`, so it has a pole at `s = 1 + u * I`, where cancellation
would instead make `continuedLFunctionOfWeight χ` holomorphic. The trivial weight
(`TauCeti.not_hasCancellation_one`) and its purely imaginary norm twists
(`TauCeti.not_hasCancellation_normTwist_one`) are the cases a character-family argument meets:
it must not assume cancellation for the degenerate members of its family.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 1 (partial summation).
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.1.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII §6, for the partial-sum bound of finite-order
  ray class character L-series.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open _root_.Filter _root_.Asymptotics _root_.IsDedekindDomain _root_.MeasureTheory
open scoped _root_.ComplexConjugate _root_.nonZeroDivisors _root_.NumberField _root_.Topology

variable {K : Type*} [Field K] [NumberField K]





/-- **Cancellation is an asymptotic bound.** A weight has cancellation exactly when its ideal
partial sums are `O(x ^ (1 - 1 / [K : ℚ]))` as `x → ∞`: on any bounded range of cutoffs `x ≥ 1`
the partial sums are bounded by an ideal count, so the eventual bound is uniform. -/
theorem solution {χ : _root_.TauCeti.UnitaryIdealWeight K} :
    _root_.TauCeti.HasCancellation χ ↔
      (fun x : ℝ ↦ _root_.TauCeti.idealSummatory K χ.toIdealArithmeticFunction x) =O[_root_.Filter.atTop]
        fun x : ℝ ↦ x ^ (1 - 1 / (_root_.Module.finrank ℚ K : ℝ)) := by
  set θ : ℝ := 1 - 1 / (_root_.Module.finrank ℚ K : ℝ)
  constructor
  · rintro ⟨C, hC⟩
    refine _root_.Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [_root_.Filter.eventually_ge_atTop 1] with x hx
    rw [_root_.Real.norm_of_nonneg (by positivity)]
    exact hC x hx
  · intro h
    obtain ⟨c, hc⟩ := h.bound
    obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hc
    have hθ : 0 ≤ θ := by
      have hd : (1 : ℝ) ≤ _root_.Module.finrank ℚ K := by exact_mod_cast _root_.Module.finrank_pos
      exact sub_nonneg.mpr ((_root_.div_le_one (zero_lt_one.trans_le hd)).mpr hd)
    set M : ℝ := ∑ k ∈ _root_.Finset.Icc 1 ⌊x₀⌋₊, ‖_root_.TauCeti.normCoeff K (1 : _root_.TauCeti.IdealArithmeticFunction K) k‖
    have hM : 0 ≤ M := _root_.Finset.sum_nonneg fun _ _ ↦ _root_.norm_nonneg _
    refine ⟨_root_.Max.max c M, fun x hx ↦ ?_⟩
    have hxθ : 1 ≤ x ^ θ := _root_.Real.one_le_rpow hx hθ
    rcases _root_.le_total x₀ x with hx₀x | hxx₀
    · have hbound := hx₀ x hx₀x
      rw [_root_.Real.norm_of_nonneg (by positivity)] at hbound
      exact hbound.trans (_root_.mul_le_mul_of_nonneg_right (_root_.le_max_left _ _) (by positivity))
    · calc ‖_root_.TauCeti.idealSummatory K χ.toIdealArithmeticFunction x‖
          ≤ ∑ k ∈ _root_.Finset.Icc 1 ⌊x⌋₊, ‖_root_.TauCeti.normCoeff K χ.toIdealArithmeticFunction k‖ := by
            rw [_root_.TauCeti.idealSummatory_eq_sum_Icc_normCoeff]
            exact _root_.norm_sum_le _ _
        _ ≤ M := (_root_.Finset.sum_le_sum fun k _ ↦
              _root_.TauCeti.UnitaryIdealWeight.norm_normCoeff_le_norm_normCoeff_one K χ k).trans
            (_root_.Finset.sum_le_sum_of_subset_of_nonneg
              (_root_.Finset.Icc_subset_Icc_right (_root_.Nat.floor_mono hxx₀)) fun _ _ _ ↦ _root_.norm_nonneg _)
        _ ≤ _root_.Max.max c M * x ^ θ :=
            (_root_.le_max_right c M).trans (_root_.le_mul_of_one_le_right (hM.trans (_root_.le_max_right c M)) hxθ)









/-!
### Deleting finitely many Euler factors
-/

















/-!
### Conjugation and imaginary norm twists
-/







/-!
### The rejection test: weights that are norm twists on their good ideals
-/









end TauCeti

end
end
