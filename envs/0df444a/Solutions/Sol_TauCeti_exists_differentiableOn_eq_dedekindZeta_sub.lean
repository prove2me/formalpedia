-- Prove2me | solution 1 for TauCeti.exists_differentiableOn_eq_dedekindZeta_sub
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T22:05:58.716649+00:00
-- url     : https://prove2.me/submissions/786c64ed-20b3-4da6-9fc2-47517814e8a2

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_NormCoeff
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Trivial
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_Order_Northcott_Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.UniformSpace.Real
import Theorems.Thm_TauCeti_LSeriesSummable_normCoeff_one_iff
import Theorems.Thm_TauCeti_LSeries_differentiableOn_mul_integral_of_isBigO
import Theorems.Thm_TauCeti_idealSummatory_eq_sum_range_normFiber
import Theorems.Thm_TauCeti_isBigO_card_idealsLE_sub

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
# Finite real-cutoff carriers for Northcott functions

This file packages the finite carrier selected by a real cutoff for a natural-valued Northcott
function, together with generic summatory functions over that carrier. The carrier depends only
on the integer part of the cutoff, and for a nonnegative cutoff it agrees with the one selected by
its natural floor.
-/

 section

namespace TauCeti

open Filter
open scoped Topology

variable {ι : Type*} (N : ι → ℕ) [Northcott N]























/-! ### Generic summatory functions -/



/-- Evaluating `summatory N w` at `x` gives the finite sum of `w` over `normLE N x`. -/
theorem summatory_apply {M : Type*} [AddCommMonoid M] (w : ι → M) (x : ℝ) :
    summatory N w x = ∑ i ∈ normLE N x, w i := by
  rw [summatory]





























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









/-- An ideal summatory function is the sum of its weight over the inclusive cutoff carrier. -/
theorem idealSummatory_apply {M : Type*} [AddCommMonoid M] (w : (Ideal (𝓞 K))⁰ → M) (x : ℝ) :
    idealSummatory K w x = ∑ I ∈ idealsLE K x, w I :=
  summatory_apply _ w x























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
# The trivial ideal weight and Dedekind zeta coefficients

This file identifies the norm coefficients of the trivial ideal weight with the coefficients of
the Dedekind zeta function.  There is one necessary exception: Mathlib's coefficient counts all
integral ideals and therefore has value `1` at index zero, contributed by the zero ideal, whereas
an `ArithmeticFunction` has value zero there.  Since `LSeries` ignores its zero coefficient, the
two coefficient systems define the same series.

For the rational field the ring of integers is isomorphic to `ℤ`.  Mapping an ideal through this
isomorphism and using `Int.ideal_span_absNorm_eq_self` shows that there is exactly one ideal of
each positive norm.  Thus the trivial ideal weight over `ℚ` regroups to the constant coefficient
`1` at every positive index, as for the Riemann zeta function.

## Roadmap role

This is Layer **1.3**, the trivial specialization, of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.  It completes Layer 1 without asserting the
exact abscissa of convergence; that is Layer 5, proved in
`TauCeti.abscissaOfAbsConv_normCoeff_one`.
-/

 section

namespace TauCeti

open scoped _root_.nonZeroDivisors _root_.NumberField

variable (K : Type*) [Field K] [NumberField K]





/-- The Dedekind zeta function is the `LSeries` of `dedekindZetaCoeff`. -/
theorem dedekindZeta_eq_LSeries_dedekindZetaCoeff (s : ℂ) :
    NumberField.dedekindZeta K s = LSeries (fun n ↦ (dedekindZetaCoeff K n : ℂ)) s := by
  simp [NumberField.dedekindZeta, dedekindZetaCoeff]

private def normFiberSubtypeEquiv {n : ℕ} (hn : n ≠ 0) :
    {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) = n} ≃
      {I : Ideal (𝓞 K) // Ideal.absNorm I = n} where
  toFun I := ⟨I.1, I.2⟩
  invFun I :=
    ⟨⟨I.1, by
      rw [← Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors]
      exact fun hzero ↦ hn (I.2.symm.trans hzero)⟩, I.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Away from zero, the cardinality of the finite nonzero-ideal norm fibre is the corresponding
Dedekind zeta coefficient. -/
theorem card_normFiber_eq_dedekindZetaCoeff {n : ℕ} (hn : n ≠ 0) :
    (normFiber K n).card = dedekindZetaCoeff K n := by
  rw [← Nat.card_eq_finsetCard, dedekindZetaCoeff]
  exact Nat.card_congr <|
    (Equiv.subtypeEquivRight fun I ↦ mem_normFiber (K := K)).trans
      (normFiberSubtypeEquiv K hn)

/-- The trivial ideal arithmetic function regroups to the Dedekind zeta coefficients away from
zero.  At zero its norm coefficient is forced to vanish by the `ArithmeticFunction` carrier. -/
@[simp]
theorem normCoeff_one_apply (n : ℕ) :
    normCoeff K (1 : IdealArithmeticFunction K) n =
      if n = 0 then 0 else dedekindZetaCoeff K n := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn, normCoeff_eq_sum_normFiber]
    simp [card_normFiber_eq_dedekindZetaCoeff K hn]

















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















/-- The Dedekind zeta series converges exactly on the open half-plane `Re s > 1`. -/
@[simp]
theorem LSeriesSummable_dedekindZetaCoeff_iff {s : ℂ} :
    LSeriesSummable (fun n ↦ (dedekindZetaCoeff K n : ℂ)) s ↔ 1 < s.re := by
  rw [← LSeriesSummable_normCoeff_one_iff K]
  exact LSeriesSummable_congr s fun {n} hn ↦ by rw [normCoeff_one_apply, if_neg hn]

end TauCeti

end
end

section
set_option autoImplicit true
namespace TauCeti.GlobalNumberFields
end TauCeti.GlobalNumberFields
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The Dedekind zeta function across the line `Re s = 1`

Let `K` be a number field of degree `d = [K : ℚ]`. The number of nonzero integral ideals of `𝓞 K`
of absolute norm at most `x` is `ρ x + O(x ^ (1 - 1 / d))`, where `ρ = dedekindZeta_residue K`:
summing the ray class ideal counts over the classes of the trivial modulus recovers the total
count, and every class has the same main term.

By partial summation this power saving continues the Dedekind zeta function across the line
`Re s = 1`, with a single simple pole there. Comparing the Dirichlet coefficients of `ζ_K` with
`ρ` times those of the Riemann zeta function, the difference has partial sums `O(n ^ (1 - 1 / d))`,
so its `L`-series continues holomorphically to `Re s > 1 - 1 / d`; and `ζ(s) - 1 / (s - 1)` is
entire (Mathlib's `riemannZeta₀`). Hence `ζ_K(s) - ρ / (s - 1)` agrees on `Re s > 1` with a
function holomorphic on `Re s > 1 - 1 / d`.

Deleting finitely many Euler factors multiplies `ζ_K` by the entire function
`∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-s))`, so the Dedekind zeta function with the Euler factors at a finite set
`S` of primes deleted has the same kind of continuation, with residue
`ρ * ∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-1))` at its simple pole `s = 1`. This is the `L`-series of the trivial
member of a family of ideal weights with bad primes `S`, such as the trivial Galois character of a
Galois extension, whose bad primes are the ramified ones.

## Main results

* `TauCeti.setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re`: the closed half-plane
  `Re s ≥ 1` lies in the half-plane of continuation.
* `TauCeti.isBigO_card_idealsLE_sub`: the number of nonzero integral ideals of norm at most `x` is
  `ρ x + O(x ^ (1 - 1 / [K : ℚ]))`.
* `TauCeti.exists_differentiableOn_eq_dedekindZeta_sub`: `ζ_K(s) - ρ / (s - 1)` extends
  holomorphically from `Re s > 1` to `Re s > 1 - 1 / [K : ℚ]`.
* `TauCeti.exists_differentiableOn_eq_LSeries_ofBadPrimes_sub`: the same for the Dedekind zeta
  function with the Euler factors at a finite set of primes deleted, with the correspondingly
  corrected residue.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VI and Chapter VIII, §3.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.1.
-/

 section

open _root_.Asymptotics _root_.Filter _root_.IsDedekindDomain _root_.NumberField _root_.TauCeti.GlobalNumberFields
open scoped _root_.nonZeroDivisors

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

/-- The closed half-plane `Re s ≥ 1` lies in the half-plane of the Dedekind zeta continuation. -/
theorem TauCeti.setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re
    (K : Type*) [_root_.Field K] [_root_.NumberField K] :
    {s : ℂ | 1 ≤ s.re} ⊆ {s : ℂ | 1 - 1 / (_root_.Module.finrank ℚ K : ℝ) < s.re} :=
  fun _ hs ↦
    (_root_.sub_lt_self (1 : ℝ) (one_div_pos.mpr (Nat.cast_pos.mpr _root_.Module.finrank_pos))).trans_le hs

variable (K : Type*) [Field K] [NumberField K]

-- The nonzero integral ideals of norm at most `x` are those prime to the trivial modulus.




-- The Dirichlet coefficients of `ζ_K` minus `ρ` times those of the Riemann zeta function have
-- partial sums `O(n ^ (1 - 1 / [K : ℚ]))`.
private theorem TauCeti.isBigO_sum_Icc_dedekindZetaCoeff_sub :
    (fun n : ℕ ↦ ∑ k ∈ _root_.Finset.Icc 1 n, ((fun k ↦ (_root_.TauCeti.dedekindZetaCoeff K k : ℂ)) -
        (_root_.NumberField.dedekindZeta_residue K : ℂ) • (1 : ℕ → ℂ)) k) =O[_root_.Filter.atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (1 - 1 / (_root_.Module.finrank ℚ K : ℝ)) := by
  -- The partial sums of the coefficients of `ζ_K` count the ideals of norm at most `n`.
  have hcount (n : ℕ) : ∑ k ∈ _root_.Finset.Icc 1 n, (_root_.TauCeti.dedekindZetaCoeff K k : ℂ) =
      ((_root_.TauCeti.idealsLE K n).card : ℂ) := by
    have h := _root_.TauCeti.idealSummatory_eq_sum_Icc_normCoeff K 1 n
    rw [_root_.TauCeti.idealSummatory_apply, _root_.Nat.floor_natCast] at h
    simp only [_root_.Pi.one_apply, _root_.Finset.sum_const, _root_.nsmul_eq_mul, _root_.mul_one] at h
    rw [h]
    refine _root_.Finset.sum_congr _root_.rfl fun k hk ↦ ?_
    rw [_root_.TauCeti.normCoeff_one_apply, _root_.if_neg (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hk).1)]
  have hsum (n : ℕ) : ∑ k ∈ _root_.Finset.Icc 1 n, ((fun k ↦ (_root_.TauCeti.dedekindZetaCoeff K k : ℂ)) -
      (_root_.NumberField.dedekindZeta_residue K : ℂ) • (1 : ℕ → ℂ)) k =
      (((_root_.TauCeti.idealsLE K n).card : ℝ) - _root_.NumberField.dedekindZeta_residue K * n : ℝ) := by
    simp [_root_.Finset.sum_sub_distrib, hcount, _root_.mul_comm]
  simp_rw [hsum, _root_.one_div]
  exact Complex.isBigO_ofReal_left.mpr
    ((_root_.TauCeti.isBigO_card_idealsLE_sub K).comp_tendsto _root_.tendsto_natCast_atTop_atTop)

/-- **The Dedekind zeta function across `Re s = 1`.** There is a function holomorphic on the
half-plane `Re s > 1 - 1 / [K : ℚ]` that agrees with `ζ_K(s) - ρ / (s - 1)` on `Re s > 1`, where
`ρ = dedekindZeta_residue K`. So `ζ_K` continues meromorphically to `Re s > 1 - 1 / [K : ℚ]`, with a
single pole, simple with residue `ρ`, at `s = 1`. -/
theorem solution : ∃ G : ℂ → ℂ,
    _root_.DifferentiableOn ℂ G {s | 1 - 1 / (_root_.Module.finrank ℚ K : ℝ) < s.re} ∧
      ∀ s : ℂ, 1 < s.re → G s = _root_.NumberField.dedekindZeta K s - _root_.NumberField.dedekindZeta_residue K / (s - 1) := by
  have hO := _root_.TauCeti.isBigO_sum_Icc_dedekindZetaCoeff_sub K
  generalize hf : (fun k ↦ (_root_.TauCeti.dedekindZetaCoeff K k : ℂ)) -
    (_root_.NumberField.dedekindZeta_residue K : ℂ) • (1 : ℕ → ℂ) = f at hO
  -- The partial-summation integral of `f` continues `LSeries f`; add `ρ (ζ(s) - 1 / (s - 1))`.
  refine ⟨fun s ↦ s * (∫ t in _root_.Set.Ioi (1 : ℝ), (∑ k ∈ _root_.Finset.Icc 1 ⌊t⌋₊, f k) *
      (t : ℂ) ^ (-(s + 1))) + _root_.NumberField.dedekindZeta_residue K * _root_.riemannZeta₀ s,
    (_root_.TauCeti.LSeries.differentiableOn_mul_integral_of_isBigO f hO).fun_add
      (differentiable_riemannZeta₀.const_mul _).differentiableOn, fun s hs ↦ ?_⟩
  have hr : 0 ≤ 1 - 1 / (_root_.Module.finrank ℚ K : ℝ) :=
    sub_nonneg.mpr (_root_.div_le_one_of_le₀ (Nat.one_le_cast.mpr _root_.Module.finrank_pos) (_root_.Nat.cast_nonneg _))
  have hsζ : _root_.LSeriesSummable (fun k ↦ (_root_.TauCeti.dedekindZetaCoeff K k : ℂ)) s :=
    (_root_.TauCeti.LSeriesSummable_dedekindZetaCoeff_iff K).mpr hs
  have hs1 : _root_.LSeriesSummable ((_root_.NumberField.dedekindZeta_residue K : ℂ) • (1 : ℕ → ℂ)) s :=
    _root_.LSeriesSummable.smul _ (LSeriesSummable_one_iff.mpr hs)
  have hs0 : s ≠ 1 := fun h ↦ by simp [h] at hs
  have hrs : 1 - 1 / (_root_.Module.finrank ℚ K : ℝ) < s.re :=
    _root_.TauCeti.setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K hs.le
  dsimp only
  rw [← _root_.LSeries_eq_mul_integral f hr hrs (hf ▸ hsζ.sub hs1) hO, ← hf, _root_.LSeries_sub hsζ hs1,
    _root_.LSeries_smul, _root_.LSeries_one_eq_riemannZeta hs, _root_.riemannZeta_eq_inv_sub_add hs0,
    _root_.TauCeti.dedekindZeta_eq_LSeries_dedekindZetaCoeff]
  ring



end TauCeti

end
end
