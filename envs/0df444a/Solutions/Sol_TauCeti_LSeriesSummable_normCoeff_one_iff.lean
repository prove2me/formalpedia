-- Prove2me | solution 1 for TauCeti.LSeriesSummable_normCoeff_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:37:46.077623+00:00
-- url     : https://prove2.me/submissions/301556b2-8dc1-4724-ae4c-49a7b9405c5f

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Estimates
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
import Theorems.Thm_TauCeti_idealCount_linearBounds
import Theorems.Thm_TauCeti_not_LSeriesSummable_normCoeff_one
import Theorems.Thm_TauCeti_sum_norm_normCoeff_one

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







/-! ### Two-sided linear bounds -/











/-! ### Partial sums of the trivial norm coefficients -/







/-! ### The exact abscissa of the trivial ideal weight -/

/-- The upper linear ideal count makes the partial sums of the trivial norm coefficients `O(n)`. -/
theorem TauCeti.isBigO_sum_norm_normCoeff_one :
    (fun n : ℕ ↦ ∑ k ∈ _root_.Finset.Icc 1 n, ‖_root_.TauCeti.normCoeff K (1 : _root_.TauCeti.IdealArithmeticFunction K) k‖)
      =O[_root_.Filter.atTop] fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) := by
  obtain ⟨b⟩ := _root_.TauCeti.idealCount_linearBounds K
  refine _root_.Asymptotics.IsBigO.of_bound b.upper ?_
  filter_upwards [_root_.Filter.eventually_ge_atTop 1] with n hn
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [_root_.TauCeti.sum_norm_normCoeff_one, _root_.Real.rpow_one, _root_.Real.norm_natCast, _root_.Real.norm_natCast]
  exact b.card_le n h1

/-- The Dirichlet series of the trivial ideal weight converges absolutely on `Re s > 1`. -/
theorem TauCeti.abscissaOfAbsConv_normCoeff_one_le :
    _root_.LSeries.abscissaOfAbsConv (_root_.TauCeti.normCoeff K (1 : _root_.TauCeti.IdealArithmeticFunction K)) ≤ 1 := by
  refine _root_.LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1) fun y hy ↦ ?_
  exact _root_.LSeriesSummable_of_sum_norm_bigO (_root_.TauCeti.isBigO_sum_norm_normCoeff_one K) _root_.zero_le_one
    (by simpa using hy)











/-! ### The exact abscissa, and its Dedekind zeta form -/

/-- **The exact abscissa of absolute convergence of the trivial ideal weight is `1`.**

The upper linear ideal count on its own supplies convergence on `Re s > 1`, and the two counts
together supply divergence at `s = 1`; no analytic continuation of the Dedekind zeta function, and
no knowledge of its pole, is involved. -/
@[simp]
theorem TauCeti.abscissaOfAbsConv_normCoeff_one :
    _root_.LSeries.abscissaOfAbsConv (_root_.TauCeti.normCoeff K (1 : _root_.TauCeti.IdealArithmeticFunction K)) = 1 := by
  refine _root_.le_antisymm (_root_.TauCeti.abscissaOfAbsConv_normCoeff_one_le K) ?_
  by_contra h
  exact _root_.TauCeti.not_LSeriesSummable_normCoeff_one K
    (_root_.LSeriesSummable_of_abscissaOfAbsConv_lt_re (s := 1) (by simpa using not_le.mp h))

/-- The Dirichlet series of the trivial ideal weight converges exactly on the open half-plane
`Re s > 1`; on the line `Re s = 1` it diverges. -/

theorem solution {s : ℂ} :
    _root_.LSeriesSummable (_root_.TauCeti.normCoeff K (1 : _root_.TauCeti.IdealArithmeticFunction K)) s ↔ 1 < s.re := by
  refine ⟨fun h ↦ ?_, fun h ↦ _root_.LSeriesSummable_of_abscissaOfAbsConv_lt_re ?_⟩
  · have h1 : (1 : ℝ) ≤ s.re := by
      have hle := h.abscissaOfAbsConv_le
      rw [_root_.TauCeti.abscissaOfAbsConv_normCoeff_one K] at hle
      exact_mod_cast hle
    rcases h1.lt_or_eq with h2 | h2
    · exact h2
    · exact _root_.absurd
        ((_root_.LSeriesSummable_iff_of_re_eq_re (s' := 1) (by rw [_root_.Complex.one_re, ← h2])).mp h)
        (_root_.TauCeti.not_LSeriesSummable_normCoeff_one K)
  · rw [_root_.TauCeti.abscissaOfAbsConv_normCoeff_one K]
    exact_mod_cast h













end TauCeti

end
end
