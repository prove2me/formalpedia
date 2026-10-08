-- Prove2me | solution 1 for ThreeSumApsp.Theorem21.hasNegativeTriangle_iff
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T08:24:06.356972+00:00
-- url     : https://prove2.me/submissions/4d999491-1fec-4390-9fb9-b85d415a3ae1

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Theorem21b_NegativeTriangle
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false



/-!
# Theorem 21(b): Negative Triangle reduces to Exact Triangle

[VW13, Theorem 3.3] in the form needed for Theorem 21(b): one question about a negative triangle
becomes `O(log U)` questions about a zero triangle.  Shifting the weights turns "the triangle is
negative" into `x + y < v` for natural numbers (`S_neg_iff`).  Let the gap at level `ℓ` be
`⌊2v/2^ℓ⌋ - ⌊2x/2^ℓ⌋ - ⌊2y/2^ℓ⌋` (`prefixGap`).  If `x + y < v`, the gap at level 0 is
`2(v - x - y) ≥ 2`, which is why the numbers are doubled; from one level to the next a gap of at
least 4 stays at least 2, and the gap is below 2 once `2^ℓ > v`.  So at some level the gap is
exactly 2 or exactly 3, and conversely a gap of at least 2 gives `x + y < v`
(`lt_iff_exists_prefixGap`).  "The gap is `e`" is an exact condition on a triangle (`negToExact`,
`negToExact_isZeroTriangle_iff`).  Together: `hasNegativeTriangle_iff` and
`theorem_21b_negative_to_exact`.
-/

@[expose] public section

namespace ThreeSumApsp

namespace Theorem21






/-- A gap of at least 2 gives `x + y < v`: with `X`, `Y`, `V` for the three prefixes,
`2x + 2y < (X + Y + 2) 2^ℓ ≤ V 2^ℓ ≤ 2v`. -/
private theorem add_lt_of_two_le_prefixGap {x y v ℓ : ℕ} (h : 2 ≤ prefixGap x y v ℓ) :
    x + y < v := by
  unfold prefixGap at h
  have hpos : 0 < 2 ^ ℓ := Nat.pow_pos (by norm_num)
  have hV := Nat.mul_div_le (2 * v) (2 ^ ℓ)
  have hX := Nat.div_add_mod (2 * x) (2 ^ ℓ)
  have hXrem := Nat.mod_lt (2 * x) hpos
  have hY := Nat.div_add_mod (2 * y) (2 ^ ℓ)
  have hYrem := Nat.mod_lt (2 * y) hpos
  have hmul : 2 ^ ℓ * (2 * x / 2 ^ ℓ + 2 * y / 2 ^ ℓ + 2) ≤ 2 ^ ℓ * (2 * v / 2 ^ ℓ) :=
    Nat.mul_le_mul_left _ (by omega)
  rw [Nat.mul_add, Nat.mul_add] at hmul
  omega

/-- A gap of at least 2 needs `2^ℓ ≤ v`: the prefix `V` of `2v` is at least 2, so
`2 · 2^ℓ ≤ V 2^ℓ ≤ 2v`. -/
private theorem pow_le_of_two_le_prefixGap {x y v ℓ : ℕ} (h : 2 ≤ prefixGap x y v ℓ) :
    2 ^ ℓ ≤ v := by
  unfold prefixGap at h
  have hX := Int.natCast_nonneg (2 * x / 2 ^ ℓ)
  have hY := Int.natCast_nonneg (2 * y / 2 ^ ℓ)
  have hV := Nat.mul_div_le (2 * v) (2 ^ ℓ)
  have hmul : 2 ^ ℓ * 2 ≤ 2 ^ ℓ * (2 * v / 2 ^ ℓ) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- A gap of at least 4 leaves a gap of at least 2 at the next level: a prefix at level `ℓ + 1` is
half the prefix at level `ℓ`, rounded down, so the new gap is at least `(4 - 1)/2`. -/
private theorem two_le_prefixGap_succ {x y v ℓ : ℕ} (h : 4 ≤ prefixGap x y v ℓ) :
    2 ≤ prefixGap x y v (ℓ + 1) := by
  unfold prefixGap at h ⊢
  rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  omega

/-- Climbing from a level at which the gap is at least 2, the first level at which the gap is below
4 has gap 2 or 3.  There is such a level, because a gap of at least 2 needs `2^ℓ ≤ v`. -/
private theorem exists_prefixGap_eq {x y v ℓ : ℕ} (h : 2 ≤ prefixGap x y v ℓ) :
    ∃ ℓ' : ℕ, prefixGap x y v ℓ' = 2 ∨ prefixGap x y v ℓ' = 3 := by
  induction hk : v + 1 - ℓ generalizing ℓ with
  | zero =>
    -- The level cannot be above `v`, since `ℓ < 2^ℓ ≤ v`.
    have hle := pow_le_of_two_le_prefixGap h
    have hlt : ℓ < 2 ^ ℓ := Nat.lt_two_pow_self
    omega
  | succ k ih =>
    by_cases h4 : 4 ≤ prefixGap x y v ℓ
    · exact ih (two_le_prefixGap_succ h4) (by omega)
    · exact ⟨ℓ, by omega⟩

/-- For Theorem 21(b), after [VW13, Proposition 3.4]: whether a triangle has negative weight is
expressed by O(log U) equations between binary prefixes of the shifted weights.
One way to write this: for natural numbers with `v < 2^L`, `x + y < v` if and only if
at one of the levels `ℓ < L` the gap `⌊2v/2^ℓ⌋ - ⌊2x/2^ℓ⌋ - ⌊2y/2^ℓ⌋` is exactly 2 or exactly 3.
(This form need not be literally the one of [VW13].) -/
private theorem lt_iff_exists_prefixGap {x y v L : ℕ} (hL : v < 2 ^ L) :
    x + y < v ↔ ∃ ℓ < L, ∃ e : ℤ, (e = 2 ∨ e = 3) ∧ prefixGap x y v ℓ = e := by
  constructor
  · intro h
    -- At level 0 the gap is `2(v - x - y) ≥ 2`.
    have hzero : 2 ≤ prefixGap x y v 0 := by
      simp only [prefixGap, pow_zero, Nat.div_one]
      omega
    obtain ⟨ℓ, hℓ⟩ := exists_prefixGap_eq hzero
    have hle : 2 ^ ℓ ≤ v := pow_le_of_two_le_prefixGap (x := x) (y := y) (by omega)
    exact ⟨ℓ, (Nat.pow_lt_pow_iff_right (by norm_num)).mp (hle.trans_lt hL), _, hℓ, rfl⟩
  · rintro ⟨ℓ, -, e, he, h⟩
    exact add_lt_of_two_le_prefixGap (ℓ := ℓ) (by omega)
























/-- A triangle has weight zero in the instance for `ℓ` and `e` exactly if the gap at level `ℓ` is
`e`. -/
private theorem negToExact_isZeroTriangle_iff {n : ℕ} (T : TriangleInstance ℤ n) (U ℓ : ℕ) (e : ℤ)
    (a b c : Fin n) :
    (T.mapWeights (negToExact U ℓ e)).IsZeroTriangle a b c ↔
      prefixGap (T.wAB a b + U).toNat (T.wBC b c + U).toNat (2 * U - T.wAC a c).toNat ℓ = e := by
  simp only [TriangleInstance.IsZeroTriangle, TriangleInstance.S, TriangleInstance.mapWeights,
    negToExact, prefixGap]
  constructor <;> intro h <;> linarith [h]

/-- A triangle is negative exactly if the shifted weights satisfy `x + y < v`. -/
private theorem S_neg_iff {n : ℕ} (T : TriangleInstance ℤ n) (U : ℕ)
    (hT : T.WeightsBoundedBy (U : ℤ)) (a b c : Fin n) :
    T.S a b c < 0 ↔
      (T.wAB a b + U).toNat + (T.wBC b c + U).toNat < (2 * U - T.wAC a c).toNat := by
  obtain ⟨hTAB, hTBC, hTAC⟩ := hT
  have hAB := abs_le.mp (hTAB a b)
  have hBC := abs_le.mp (hTBC b c)
  have hAC := abs_le.mp (hTAC a c)
  simp only [TriangleInstance.S]
  omega

/-- The reduction of [VW13, Theorem 3.3], for weights in `[-U, U]` with `3U < 2^L`: there is a
negative triangle if and only if, at one of the levels `ℓ < L` and for `e = 2` or `e = 3`, the
instance made of the prefixes has a zero triangle. -/
theorem hasNegativeTriangle_iff_sourceProof {n U L : ℕ} (T : TriangleInstance ℤ n)
    (hT : T.WeightsBoundedBy (U : ℤ)) (hL : 3 * U < 2 ^ L) :
    T.HasNegativeTriangle ↔ ∃ ℓ < L, ∃ e : ℤ, (e = 2 ∨ e = 3) ∧
      (T.mapWeights (negToExact U ℓ e)).HasZeroTriangle := by
  have hv (a c : Fin n) : (2 * U - T.wAC a c).toNat < 2 ^ L := by
    obtain ⟨-, -, hTAC⟩ := hT
    have := abs_le.mp (hTAC a c)
    omega
  constructor
  · rintro ⟨a, b, c, h⟩
    obtain ⟨ℓ, hℓ, e, he, hgap⟩ :=
      (lt_iff_exists_prefixGap (hv a c)).1 ((S_neg_iff T U hT a b c).1 h)
    exact ⟨ℓ, hℓ, e, he, a, b, c, (negToExact_isZeroTriangle_iff T U ℓ e a b c).2 hgap⟩
  · rintro ⟨ℓ, hℓ, e, he, a, b, c, h⟩
    exact ⟨a, b, c, (S_neg_iff T U hT a b c).2 ((lt_iff_exists_prefixGap (hv a c)).2
      ⟨ℓ, hℓ, e, he, (negToExact_isZeroTriangle_iff T U ℓ e a b c).1 h⟩)⟩














end Theorem21




































end ThreeSumApsp

end


theorem solution : ∀ {n U L : Nat} (T : ThreeSumApsp.TriangleInstance Int n),
  @ThreeSumApsp.TriangleInstance.WeightsBoundedBy Int instLatticeInt Int.instAddGroup n T
      (@Nat.cast.{0} Int instNatCastInt U) →
    @LT.lt.{0} Nat instLTNat
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) U)
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L) →
      Iff
        (@ThreeSumApsp.TriangleInstance.HasNegativeTriangle Int Int.instAdd
          (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring)) Int.instLTInt n T)
        (∃ (ℓ : Nat),
          And (@LT.lt.{0} Nat instLTNat ℓ L)
            (∃ (e : Int),
              And
                (Or (@Eq.{1} Int e (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))
                  (@Eq.{1} Int e (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3)))))
                (@ThreeSumApsp.TriangleInstance.HasZeroTriangle Int Int.instAdd
                  (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring)) n
                  (@ThreeSumApsp.TriangleInstance.mapWeights n T (ThreeSumApsp.Theorem21.negToExact U ℓ e))))) := by
  exact @ThreeSumApsp.Theorem21.hasNegativeTriangle_iff_sourceProof

#print axioms solution
