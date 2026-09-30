-- Prove2me | solution 1 for TauCeti.idealCount_linearBounds
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:15:58.489425+00:00
-- url     : https://prove2.me/submissions/12903dd0-2fc0-418d-ada6-b9bedf764a65

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Estimates
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

/-- The number of nonzero integral ideals of bounded absolute norm is monotone in the cutoff. -/
theorem TauCeti.card_absNorm_real_le_mono {x y : ℝ} (h : x ≤ y) :
    _root_.Nat.card {I : (_root_.Ideal (𝓞 K))⁰ // (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ) ≤ x} ≤
      _root_.Nat.card {I : (_root_.Ideal (𝓞 K))⁰ // (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ) ≤ y} := by
  have : _root_.Finite {I : (_root_.Ideal (𝓞 K))⁰ // (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ) ≤ y} :=
    (_root_.TauCeti.finite_setOf_absNorm_real_le K y).to_subtype
  refine _root_.Nat.card_le_card_of_injective (fun I ↦ ⟨I.1, I.2.trans h⟩) fun a b hab ↦ ?_
  injection hab with hab'
  exact _root_.Subtype.ext hab'

/-- From cutoff `1` on there is at least one nonzero integral ideal of bounded absolute norm,
namely the unit ideal. -/
theorem TauCeti.one_le_card_absNorm_real_le {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ _root_.Nat.card {I : (_root_.Ideal (𝓞 K))⁰ // (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ) ≤ x} := by
  have hfin : _root_.Finite {I : (_root_.Ideal (𝓞 K))⁰ // (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ) ≤ x} :=
    (_root_.TauCeti.finite_setOf_absNorm_real_le K x).to_subtype
  have hne : _root_.Nonempty {I : (_root_.Ideal (𝓞 K))⁰ // (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ) ≤ x} :=
    ⟨⟨1, by simpa using hx⟩⟩
  exact Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨hne, hfin⟩)

/-! ### Two-sided linear bounds -/



/-- **Beyond a threshold the count lies between two multiples of `x`.**  There is a cutoff
`X ≥ 1` such that every `x ≥ X` has at least `r / 2 * x` and at most `(r + 1) * x` nonzero integral
ideals of absolute norm at most `x`, where `r` is `NumberField.dedekindZeta_residue K`.

The constants are not optimal and are not meant to be: `idealCount_linearBounds` needs only that
some positive multiples of `x` sandwich the count above the cutoff. -/
private theorem TauCeti.exists_le_card_and_card_le_of_le :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x →
      _root_.NumberField.dedekindZeta_residue K / 2 * x ≤
          _root_.Nat.card {I : (_root_.Ideal (𝓞 K))⁰ // (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ) ≤ x} ∧
        (_root_.Nat.card {I : (_root_.Ideal (𝓞 K))⁰ // (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ) ≤ x} : ℝ) ≤
          (_root_.NumberField.dedekindZeta_residue K + 1) * x := by
  set r : ℝ := _root_.NumberField.dedekindZeta_residue K with hr
  have hpos : 0 < r := _root_.NumberField.dedekindZeta_residue_pos K
  have htend : _root_.Filter.Tendsto (fun x : ℝ ↦
      (_root_.Nat.card {I : (_root_.Ideal (𝓞 K))⁰ // (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ) ≤ x} : ℝ) / x)
      _root_.Filter.atTop (𝓝 r) := by
    rw [hr, _root_.NumberField.dedekindZeta_residue_def]
    exact _root_.NumberField.Ideal.tendsto_norm_le_div_atTop₀ K
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp
    (((htend.eventually_const_lt (by linarith : r / 2 < r)).and
      (htend.eventually_lt_const (by linarith : r < r + 1))).and (_root_.Filter.eventually_ge_atTop (1 : ℝ)))
  refine ⟨_root_.Max.max X₀ 1, _root_.le_max_right _ _, fun x hx ↦ ?_⟩
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hX₀ x ((_root_.le_max_left X₀ 1).trans hx)
  have hxpos : 0 < x := _root_.lt_of_lt_of_le _root_.zero_lt_one h₃
  exact ⟨(_root_.le_div_iff₀ hxpos).mp h₁.le, (_root_.div_le_iff₀ hxpos).mp h₂.le⟩

/-- **Below the threshold, `X⁻¹` serves as the lower constant.**  For `1 ≤ x ≤ X` there are at
least `X⁻¹ * x` nonzero integral ideals of absolute norm at most `x`.  This is the half of
`idealCount_linearBounds`'s lower bound that the asymptotic does not reach, and it asks for nothing
beyond `1 ≤ x ≤ X`. -/
private theorem TauCeti.inv_mul_le_card_of_le_of_le {X x : ℝ} (hx : 1 ≤ x) (hxX : x ≤ X) :
    X⁻¹ * x ≤ _root_.Nat.card {I : (_root_.Ideal (𝓞 K))⁰ // (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ) ≤ x} :=
  _root_.le_trans (_root_.inv_mul_le_one_of_le₀ hxX (zero_le_one.trans (hx.trans hxX)))
    (by exact_mod_cast _root_.TauCeti.one_le_card_absNorm_real_le K hx)

/-- **Two-sided linear ideal counts.** The number of nonzero integral ideals of absolute norm at
most `x` is bounded above and below by positive multiples of `x`, for every cutoff `x ≥ 1`.

Both constants come from Mathlib's asymptotic `NumberField.Ideal.tendsto_norm_le_div_atTop₀`,
whose limit is positive by `NumberField.dedekindZeta_residue_pos`; below the threshold produced by
that limit the bounds are secured by the unit ideal and by monotonicity of the count. -/
theorem solution : _root_.Nonempty (_root_.TauCeti.IdealCountingLinearBounds K) := by
  set r : ℝ := _root_.NumberField.dedekindZeta_residue K
  have hpos : 0 < r := _root_.NumberField.dedekindZeta_residue_pos K
  obtain ⟨X, hX1, hmain⟩ := _root_.TauCeti.exists_le_card_and_card_le_of_le K
  have hXpos : 0 < X := _root_.lt_of_lt_of_le _root_.zero_lt_one hX1
  set M : ℝ :=
    (_root_.Nat.card {I : (_root_.Ideal (𝓞 K))⁰ // (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ) ≤ X} : ℝ) with hM
  have hupos : (0 : ℝ) < _root_.Max.max (r + 1) M := _root_.lt_of_lt_of_le (by linarith) (_root_.le_max_left _ _)
  refine ⟨{
    lower := _root_.Min.min (r / 2) X⁻¹
    upper := _root_.Max.max (r + 1) M
    lower_pos := _root_.lt_min (by linarith) (inv_pos.mpr hXpos)
    upper_pos := hupos
    le_card := ?_
    card_le := ?_ }⟩
  · intro x hx
    have hxpos : 0 < x := _root_.lt_of_lt_of_le _root_.zero_lt_one hx
    rcases _root_.le_or_gt X x with hxX | hxX
    · exact _root_.le_trans (_root_.mul_le_mul_of_nonneg_right (_root_.min_le_left _ _) hxpos.le) (hmain x hxX).1
    · exact _root_.le_trans (_root_.mul_le_mul_of_nonneg_right (_root_.min_le_right _ _) hxpos.le)
        (_root_.TauCeti.inv_mul_le_card_of_le_of_le K hx hxX.le)
  · intro x hx
    have hxpos : 0 < x := _root_.lt_of_lt_of_le _root_.zero_lt_one hx
    rcases _root_.le_or_gt X x with hxX | hxX
    · exact _root_.le_trans (hmain x hxX).2 (_root_.mul_le_mul_of_nonneg_right (_root_.le_max_left _ _) hxpos.le)
    · have h1 : (_root_.Nat.card {I : (_root_.Ideal (𝓞 K))⁰ // (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ) ≤ x} : ℝ)
          ≤ M := by rw [hM]; exact_mod_cast _root_.TauCeti.card_absNorm_real_le_mono K hxX.le
      exact h1.trans ((_root_.le_max_right _ _).trans (_root_.le_mul_of_one_le_right hupos.le hx))



/-! ### Partial sums of the trivial norm coefficients -/







/-! ### The exact abscissa of the trivial ideal weight -/















/-! ### The exact abscissa, and its Dedekind zeta form -/

















end TauCeti

end
end
