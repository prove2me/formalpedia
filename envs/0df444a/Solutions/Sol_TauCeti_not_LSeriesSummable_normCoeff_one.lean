-- Prove2me | solution 1 for TauCeti.not_LSeriesSummable_normCoeff_one
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:25:29.160505+00:00
-- url     : https://prove2.me/submissions/e47ec8c6-0397-452b-b674-1da4883c72d4

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





/-- The partial sums of the trivial norm coefficients over a half-open initial interval. -/
private theorem TauCeti.sum_Ioc_norm_normCoeff_one (n : ℕ) :
    ∑ k ∈ _root_.Finset.Ioc 0 n, ‖_root_.TauCeti.normCoeff K (1 : _root_.TauCeti.IdealArithmeticFunction K) k‖
      = _root_.Nat.card {I : (_root_.Ideal (𝓞 K))⁰ // (_root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) : ℝ) ≤ (n : ℝ)} := by
  -- Normalize the order-theoretic successor in the interval rewrite to the natural numeral `1`.
  have hinterval : _root_.Finset.Icc 1 n = _root_.Finset.Ioc 0 n := by
    simpa only [_root_.Nat.succ_eq_succ] using _root_.Finset.Icc_succ_left_eq_Ioc 0 n
  rw [← _root_.TauCeti.sum_norm_normCoeff_one, hinterval]

/-- The difference of the endpoint ideal-count bounds controls the coefficient mass in a block. -/
private theorem TauCeti.lower_mul_sub_upper_mul_le_sum_Ioc_norm_normCoeff_one
    (b : _root_.TauCeti.IdealCountingLinearBounds K) {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N) :
    b.lower * ((m * N : ℕ) : ℝ) - b.upper * (N : ℝ) ≤
      ∑ k ∈ _root_.Finset.Ioc N (m * N), ‖_root_.TauCeti.normCoeff K (1 : _root_.TauCeti.IdealArithmeticFunction K) k‖ := by
  have hNM : N ≤ m * N := _root_.Nat.le_mul_of_pos_left N (_root_.lt_of_lt_of_le _root_.zero_lt_one hm)
  have hsplit : (∑ k ∈ _root_.Finset.Ioc 0 N, ‖_root_.TauCeti.normCoeff K (1 : _root_.TauCeti.IdealArithmeticFunction K) k‖)
      + ∑ k ∈ _root_.Finset.Ioc N (m * N), ‖_root_.TauCeti.normCoeff K (1 : _root_.TauCeti.IdealArithmeticFunction K) k‖
      = ∑ k ∈ _root_.Finset.Ioc 0 (m * N), ‖_root_.TauCeti.normCoeff K (1 : _root_.TauCeti.IdealArithmeticFunction K) k‖ :=
    _root_.Finset.sum_Ioc_consecutive _ (_root_.Nat.zero_le N) hNM
  have hlow : b.lower * ((m * N : ℕ) : ℝ)
      ≤ ∑ k ∈ _root_.Finset.Ioc 0 (m * N), ‖_root_.TauCeti.normCoeff K (1 : _root_.TauCeti.IdealArithmeticFunction K) k‖ := by
    rw [_root_.TauCeti.sum_Ioc_norm_normCoeff_one]
    exact b.le_card _ (by exact_mod_cast _root_.Nat.lt_of_lt_of_le hN hNM)
  have hup : (∑ k ∈ _root_.Finset.Ioc 0 N, ‖_root_.TauCeti.normCoeff K (1 : _root_.TauCeti.IdealArithmeticFunction K) k‖)
      ≤ b.upper * (N : ℝ) := by
    rw [_root_.TauCeti.sum_Ioc_norm_normCoeff_one]
    exact b.card_le _ (by exact_mod_cast hN)
  linarith

/-- Dividing all coefficients in a positive block by its right endpoint underestimates the
corresponding Dirichlet-series terms at `s = 1`. -/
private theorem TauCeti.sum_Ioc_norm_normCoeff_one_div_le_sum_Ioc_norm_term {m N : ℕ} (hN : 1 ≤ N) :
    (∑ k ∈ _root_.Finset.Ioc N (m * N), ‖_root_.TauCeti.normCoeff K (1 : _root_.TauCeti.IdealArithmeticFunction K) k‖) /
        ((m * N : ℕ) : ℝ) ≤
      ∑ k ∈ _root_.Finset.Ioc N (m * N),
        ‖_root_.LSeries.term (_root_.TauCeti.normCoeff K (1 : _root_.TauCeti.IdealArithmeticFunction K)) 1 k‖ := by
  rw [_root_.Finset.sum_div]
  refine _root_.Finset.sum_le_sum fun k hk ↦ ?_
  obtain ⟨hk1, hk2⟩ := Finset.mem_Ioc.mp hk
  have hk0 : k ≠ 0 := by omega
  have hkpos : (0 : ℝ) < k := by exact_mod_cast _root_.Nat.pos_of_ne_zero hk0
  rw [_root_.LSeries.norm_term_eq]
  simp only [_root_.Complex.one_re, _root_.if_neg hk0, _root_.Real.rpow_one]
  refine _root_.div_le_div_of_nonneg_left (_root_.norm_nonneg _) hkpos ?_
  exact_mod_cast hk2

/-- **The fixed-ratio block lower bound.** Once the block ratio `m` is at least
`2 * upper / lower`, the terms of the Dirichlet series of the trivial ideal weight at `s = 1` over
a block `N < k ≤ m N` add up to at least `lower / 2`, uniformly in `N ≥ 1`.

Both linear ideal counts enter, as a difference of endpoint counts: the lower bound at the right
endpoint `m N` and the upper bound at the left endpoint `N` leave the block at least
`lower * m N - upper * N` of coefficient mass, and every term of the block is divided by at most
`m N`. -/
private theorem TauCeti.lower_div_two_le_sum_Ioc_norm_term (b : _root_.TauCeti.IdealCountingLinearBounds K) {m N : ℕ}
    (hm : 2 * b.upper / b.lower ≤ (m : ℝ)) (hN : 1 ≤ N) :
    b.lower / 2 ≤ ∑ k ∈ _root_.Finset.Ioc N (m * N),
      ‖_root_.LSeries.term (_root_.TauCeti.normCoeff K (1 : _root_.TauCeti.IdealArithmeticFunction K)) 1 k‖ := by
  have hmpos : (0 : ℝ) < m :=
    _root_.lt_of_lt_of_le (_root_.div_pos (by linarith [b.upper_pos]) b.lower_pos) hm
  have hm1 : 1 ≤ m := by exact_mod_cast hmpos
  have hupperm : b.upper / m ≤ b.lower / 2 := by
    rw [_root_.div_le_div_iff₀ hmpos _root_.two_pos]
    have := (_root_.div_le_iff₀ b.lower_pos).mp hm
    linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hMpos : (0 : ℝ) < (m * N : ℕ) := by positivity
  refine _root_.le_trans ?_ (_root_.TauCeti.sum_Ioc_norm_normCoeff_one_div_le_sum_Ioc_norm_term K hN)
  rw [_root_.le_div_iff₀ hMpos]
  have hcast : ((m * N : ℕ) : ℝ) = (m : ℝ) * (N : ℝ) := by push_cast; ring
  have hkey : b.lower / 2 * ((m : ℝ) * N) ≤ b.lower * ((m : ℝ) * N) - b.upper * N := by
    have h2 : b.upper * (N : ℝ) ≤ b.lower / 2 * ((m : ℝ) * N) := by
      have := _root_.mul_le_mul_of_nonneg_right hupperm (_root_.le_of_lt hNpos)
      rw [_root_.div_mul_eq_mul_div, _root_.div_le_iff₀ hmpos] at this
      nlinarith
    nlinarith [b.lower_pos]
  calc b.lower / 2 * ((m * N : ℕ) : ℝ) = b.lower / 2 * ((m : ℝ) * N) := by rw [hcast]
    _ ≤ b.lower * ((m : ℝ) * N) - b.upper * N := hkey
    _ = b.lower * ((m * N : ℕ) : ℝ) - b.upper * N := by rw [hcast]
    _ ≤ ∑ k ∈ _root_.Finset.Ioc N (m * N), ‖_root_.TauCeti.normCoeff K (1 : _root_.TauCeti.IdealArithmeticFunction K) k‖ :=
      _root_.TauCeti.lower_mul_sub_upper_mul_le_sum_Ioc_norm_normCoeff_one K b hm1 hN

/-- **Divergence at `s = 1`.** The Dirichlet series of the trivial ideal weight does not converge
at `s = 1`.

The two-sided linear ideal counts are what force this: by
`TauCeti.lower_div_two_le_sum_Ioc_norm_term` every block `N < n ≤ m N` of fixed ratio
`m ≥ 2 * upper / lower` carries mass at least `lower / 2`, whereas the blocks of a convergent
series of nonnegative terms become arbitrarily small. -/
theorem solution :
    ¬ _root_.LSeriesSummable (_root_.TauCeti.normCoeff K (1 : _root_.TauCeti.IdealArithmeticFunction K)) 1 := by
  intro hsum
  obtain ⟨b⟩ := _root_.TauCeti.idealCount_linearBounds K
  set g : ℕ → ℝ := fun n ↦ ‖_root_.LSeries.term (_root_.TauCeti.normCoeff K (1 : _root_.TauCeti.IdealArithmeticFunction K)) 1 n‖
    with hgdef
  have hgsum : _root_.Summable g := summable_norm_iff.mpr hsum
  have hgnn : ∀ n, 0 ≤ g n := fun n ↦ _root_.norm_nonneg _
  set m : ℕ := ⌈2 * b.upper / b.lower⌉₊ + 1 with hmdef
  have hm1 : 1 ≤ m := _root_.Nat.le_add_left 1 _
  have hmR : 2 * b.upper / b.lower ≤ (m : ℝ) := by
    rw [hmdef]
    push_cast
    linarith [_root_.Nat.le_ceil (2 * b.upper / b.lower)]
  -- the blocks of a convergent series of nonnegative terms are eventually small
  have hpartial : _root_.Filter.Tendsto (fun N : ℕ ↦ ∑ k ∈ _root_.Finset.Ioc 0 N, g k) _root_.Filter.atTop (𝓝 (∑' k, g k)) := by
    refine (hgsum.hasSum.tendsto_sum_nat.comp (_root_.Filter.tendsto_add_atTop_nat 1)).congr fun N ↦ ?_
    simp only [_root_.Function.comp_apply]
    refine (_root_.Finset.sum_subset ?_ ?_).symm
    · intro k hk
      rw [_root_.Finset.mem_range]
      exact _root_.Nat.lt_succ_of_le (Finset.mem_Ioc.mp hk).2
    · intro k hk hknot
      have hk0 : k = 0 := by
        rcases _root_.Nat.eq_zero_or_pos k with h | h
        · exact h
        · exact _root_.absurd (Finset.mem_Ioc.mpr ⟨h, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)⟩) hknot
      rw [hk0, hgdef]
      simp
  have htail : _root_.Filter.Tendsto (fun N : ℕ ↦ (∑' k, g k) - ∑ k ∈ _root_.Finset.Ioc 0 N, g k) _root_.Filter.atTop (𝓝 0) := by
    simpa using hpartial.const_sub (∑' k, g k)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((htail.eventually_lt_const (by linarith [b.lower_pos] : (0 : ℝ) < b.lower / 2)).and
      (_root_.Filter.eventually_ge_atTop 1))
  obtain ⟨h1, h2⟩ := hN N _root_.le_rfl
  have hNM : N ≤ m * N := _root_.Nat.le_mul_of_pos_left N (_root_.lt_of_lt_of_le _root_.zero_lt_one hm1)
  have hle : ∑ k ∈ _root_.Finset.Ioc N (m * N), g k ≤ (∑' k, g k) - ∑ k ∈ _root_.Finset.Ioc 0 N, g k := by
    have hsplit : (∑ k ∈ _root_.Finset.Ioc 0 N, g k) + ∑ k ∈ _root_.Finset.Ioc N (m * N), g k
        = ∑ k ∈ _root_.Finset.Ioc 0 (m * N), g k :=
      _root_.Finset.sum_Ioc_consecutive _ (_root_.Nat.zero_le N) hNM
    have hbound : ∑ k ∈ _root_.Finset.Ioc 0 (m * N), g k ≤ ∑' k, g k :=
      hgsum.sum_le_tsum _ (fun k _ ↦ hgnn k)
    linarith
  linarith [_root_.TauCeti.lower_div_two_le_sum_Ioc_norm_term K b hmR h2]

/-! ### The exact abscissa, and its Dedekind zeta form -/

















end TauCeti

end
end
