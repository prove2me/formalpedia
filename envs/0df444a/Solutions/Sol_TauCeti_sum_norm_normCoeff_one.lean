-- Prove2me | solution 1 for TauCeti.sum_norm_normCoeff_one
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:16:00.523835+00:00
-- url     : https://prove2.me/submissions/09fc9608-9e1f-467f-9fc4-b157089101f0

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_NormCoeff
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real

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
end TauCeti
section TauCeti
open TauCeti

open _root_.Filter
open scoped _root_.nonZeroDivisors _root_.NumberField _root_.Topology _root_.ComplexOrder

variable (K : Type*) [Field K] [NumberField K]

/-! ### Finiteness and monotonicity of the ideal count -/

/-- The nonzero integral ideals of absolute norm at most a real cutoff form a finite set. -/
theorem TauCeti.finite_setOf_absNorm_real_le (x : ℝ) :
    {I : (_root_.Ideal (𝓞 K))⁰ | (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ) ≤ x}.Finite :=
  (_root_.Ideal.finite_setOfPred_absNorm_le₀ ⌊x⌋₊).subset fun _ hI ↦ _root_.Nat.le_floor hI





/-! ### Two-sided linear bounds -/











/-! ### Partial sums of the trivial norm coefficients -/

/-- The trivial ideal weight has norm coefficient the number of nonzero integral ideals of the
given absolute norm, so its absolute value is that count. -/
theorem TauCeti.norm_normCoeff_one (n : ℕ) :
    ‖_root_.TauCeti.normCoeff K (1 : _root_.TauCeti.IdealArithmeticFunction K) n‖ = (_root_.TauCeti.normFiber K n).card := by
  rw [_root_.TauCeti.normCoeff_eq_sum_normFiber]
  simp



/-- **The partial sums of the trivial norm coefficients are the ideal counts.** Summing the norm
coefficients of the trivial ideal weight over `1 ≤ k ≤ n` counts the nonzero integral ideals of
absolute norm at most `n`, because the absolute-norm fibres partition them. -/
theorem solution (n : ℕ) :
    ∑ k ∈ _root_.Finset.Icc 1 n, ‖_root_.TauCeti.normCoeff K (1 : _root_.TauCeti.IdealArithmeticFunction K) k‖
      = _root_.Nat.card {I : (_root_.Ideal (𝓞 K))⁰ // (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ) ≤ (n : ℝ)} := by
  classical
  have hfin := _root_.TauCeti.finite_setOf_absNorm_real_le K (n : ℝ)
  have key : hfin.toFinset.card = ∑ k ∈ _root_.Finset.Icc 1 n, (_root_.TauCeti.normFiber K k).card := by
    refine _root_.Finset.card_eq_sum_card_fiberwise
      (f := fun I : (_root_.Ideal (𝓞 K))⁰ ↦ _root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)))
      (t := _root_.Finset.Icc 1 n) (fun I hI ↦ ?_) |>.trans (_root_.Finset.sum_congr _root_.rfl fun k hk ↦ ?_)
    · rw [_root_.Finset.mem_coe, _root_.Finset.mem_Icc]
      refine ⟨_root_.Ideal.absNorm_pos_of_nonZeroDivisors I, ?_⟩
      rw [_root_.Finset.mem_coe, _root_.Set.Finite.mem_toFinset] at hI
      exact_mod_cast hI
    · congr 1
      ext I
      rw [_root_.Finset.mem_filter, _root_.Set.Finite.mem_toFinset, _root_.Set.mem_ofPred_eq, _root_.TauCeti.mem_normFiber]
      refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
      rw [h]
      exact_mod_cast (Finset.mem_Icc.mp hk).2
  have hcard : _root_.Nat.card {I : (_root_.Ideal (𝓞 K))⁰ // (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ) ≤ (n : ℝ)}
      = hfin.toFinset.card := _root_.Nat.card_eq_card_finite_toFinset hfin
  rw [hcard, key, _root_.Nat.cast_sum]
  exact _root_.Finset.sum_congr _root_.rfl fun k _ ↦ _root_.TauCeti.norm_normCoeff_one K k

/-! ### The exact abscissa of the trivial ideal weight -/















/-! ### The exact abscissa, and its Dedekind zeta form -/

















end TauCeti

end
end
