-- Prove2me | solution 1 for ThreeSum.WeightedScore.score_eq_remaining
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:05:49.081439+00:00
-- url     : https://prove2.me/submissions/d7ec1110-71e6-48aa-9397-06335de23e6e

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum_Arithmetic_mul_dvd_iff_of_bezout


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.Arithmetic
end ThreeSum.Arithmetic
namespace ThreeSum.ModuloCounts
end ThreeSum.ModuloCounts
namespace ThreeSum.WeightedModuli
end ThreeSum.WeightedModuli

section


/-!
# Exact arithmetic interface for the deterministic histogram construction

These are finite arithmetic and counting theorems.  They do not assert a
running-time bound or the existence of a word-RAM implementation.
-/

namespace ThreeSum.Arithmetic

open Finset
open scoped BigOperators

/-! ## Guarded arithmetic-to-radix lifts -/






















































































































/-! ## The weighted false-count identity -/
































/-- Every auxiliary test either succeeds or fails, exactly once. -/
theorem missWeight_add_hits (L : Finset ℤ) (x : ℤ) :
    missWeight L x + (∑ l ∈ L, dividesIndicator l x) = L.card := by
  unfold missWeight
  rw [← Finset.sum_add_distrib]
  calc
    (∑ l ∈ L, ((if l ∣ x then 0 else 1) + dividesIndicator l x)) =
        ∑ _l ∈ L, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro l hl
      by_cases h : l ∣ x <;> simp [dividesIndicator, h]
    _ = L.card := by simp



































































































/-! ## Exact early YES from per-original-triple representation caps -/



































































end ThreeSum.Arithmetic

end

section


/-!
# Exact auxiliary tests from the same finite prime pool

The prime pool used for deterministic contraction supplies enough distinct
primes to separate bounded nonzero differences. To use this same pool in
the weighted counting identity, the joint modulus must account for a prime
that already divides the current modulus; see `WeightedModuli.lean`.
-/

namespace ThreeSum.Auxiliary

open Finset
open scoped BigOperators



theorem moduli_card (C : Finset ℕ) : (moduli C).card = C.card := by
  exact card_image_of_injective C (show Function.Injective (fun p : ℕ => (p : ℤ)) from Nat.cast_injective)






























































end ThreeSum.Auxiliary

end

section


/-!
# Weighted counting with possibly shared prime factors

For prime `p`, simultaneous divisibility by `q` and `p` is tested at `q`
when `p ∣ q`, and at `q*p` otherwise. This executable branch permits one
finite prime pool to supply both contraction and auxiliary tests.
-/

namespace ThreeSum.WeightedModuli

open Finset Arithmetic
open scoped BigOperators
















theorem joint_dvd_iff (q p : ℕ) (hp : Nat.Prime p) (z : ℤ) :
    (joint q p : ℤ) ∣ z ↔ (q : ℤ) ∣ z ∧ (p : ℤ) ∣ z := by
  by_cases h : p ∣ q
  · simp only [joint, if_pos h]
    exact ⟨fun hz => ⟨hz, (Int.natCast_dvd_natCast.mpr h).trans hz⟩, fun hz => hz.1⟩
  · simp only [joint, if_neg h, Nat.cast_mul]
    have hc : IsCoprime (q : ℤ) (p : ℤ) :=
      ((hp.coprime_iff_not_dvd.mpr h).symm).isCoprime
    obtain ⟨u, v, huv⟩ := hc
    exact mul_dvd_iff_of_bezout ⟨u, v, huv⟩

theorem weighted_indicator (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p)
    (q : ℕ) (z : ℤ) :
    (if (q : ℤ) ∣ z then missWeight (Auxiliary.moduli C) z else 0) +
      (∑ p ∈ C, dividesIndicator (joint q p) z) =
      C.card * dividesIndicator q z := by
  have hmod : (∑ p ∈ C, dividesIndicator (p : ℤ) z) =
      ∑ p ∈ Auxiliary.moduli C, dividesIndicator p z := by
    rw [Auxiliary.moduli, Finset.sum_image]
    intro a ha b hb heq
    exact Nat.cast_injective heq
  by_cases hq : (q : ℤ) ∣ z
  · have hjoint : (∑ p ∈ C, dividesIndicator (joint q p) z) =
        ∑ p ∈ C, dividesIndicator (p : ℤ) z := by
      apply Finset.sum_congr rfl
      intro p hp
      simp [dividesIndicator, joint_dvd_iff q p (hC p hp), hq]
    rw [if_pos hq, hjoint, hmod]
    simpa [dividesIndicator, hq, Auxiliary.moduli_card] using
      missWeight_add_hits (Auxiliary.moduli C) z
  · have hjoint : (∑ p ∈ C, dividesIndicator (joint q p) z) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      simp [dividesIndicator, joint_dvd_iff q p (hC p hp), hq]
    rw [if_neg hq, hjoint]
    simp [dividesIndicator, hq]

theorem weighted_count_add {ι : Type*} (T : Finset ι) (difference : ι → ℤ)
    (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p) (q : ℕ) :
    weightedFalseCount T difference (Auxiliary.moduli C) q +
      (∑ p ∈ C, modCount T difference (joint q p)) =
      C.card * modCount T difference q := by
  unfold weightedFalseCount modCount
  calc
    _ = ∑ i ∈ T, ((if (q : ℤ) ∣ difference i then
        missWeight (Auxiliary.moduli C) (difference i) else 0) +
        ∑ p ∈ C, dividesIndicator (joint q p) (difference i)) := by
          rw [Finset.sum_add_distrib, Finset.sum_comm]
    _ = ∑ i ∈ T, C.card * dividesIndicator q (difference i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact weighted_indicator C hC q (difference i)
    _ = _ := by rw [Finset.mul_sum]

theorem weighted_count_eq {ι : Type*} (T : Finset ι) (difference : ι → ℤ)
    (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p) (q : ℕ) :
    weightedFalseCount T difference (Auxiliary.moduli C) q =
      C.card * modCount T difference q -
        (∑ p ∈ C, modCount T difference (joint q p)) := by
  have h := weighted_count_add T difference C hC q
  omega

end ThreeSum.WeightedModuli

end

section


/-!
# Array-order identities for the weighted modular score

The auxiliary primes are read in a fixed array order.  Every partial
correction is at most the initial `s * N_q`, so the corresponding machine
subtractions stay nonnegative.  Shared factors with `q` use `joint`.
-/

namespace ThreeSum.WeightedScore

open Finset Arithmetic ModuloCounts WeightedModuli
open scoped BigOperators




























































































theorem score_eq_remaining_sourceProof (primes : ℕ → ℕ) (s q nA nB nC : ℕ)
    (a b c : ℕ → ℤ)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j) :
    score primes s q nA nB nC a b c = remaining primes s q nA nB nC a b c s := by
  have hcard : (auxiliarySet primes s).card = s := by
    unfold auxiliarySet
    rw [Finset.card_image_of_injOn]
    · exact card_range s
    · intro i hi j hj heq
      exact hinj i (mem_range.mp hi) j (mem_range.mp hj) heq
  have hpr : ∀ p ∈ auxiliarySet primes s, Nat.Prime p := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
    exact hprime i (mem_range.mp hi)
  have hsum : (∑ p ∈ auxiliarySet primes s,
      modCount (triples nA nB nC) (difference a b c) (joint q p)) =
      corrections primes q nA nB nC a b c s := by
    unfold auxiliarySet corrections count
    rw [sum_image]
    intro i hi j hj heq
    exact hinj i (mem_range.mp hi) j (mem_range.mp hj) heq
  unfold score
  rw [weighted_count_eq _ _ _ hpr q, hcard, hsum]
  rfl











end ThreeSum.WeightedScore

end


theorem solution : ∀ (primes : Nat → Nat) (s q nA nB nC : Nat) (a b c : Nat → Int),
  (∀ (i : Nat), @LT.lt.{0} Nat instLTNat i s → Nat.Prime (primes i)) →
    (∀ (i : Nat),
        @LT.lt.{0} Nat instLTNat i s →
          ∀ (j : Nat), @LT.lt.{0} Nat instLTNat j s → @Eq.{1} Nat (primes i) (primes j) → @Eq.{1} Nat i j) →
      @Eq.{1} Nat (ThreeSum.WeightedScore.score primes s q nA nB nC a b c)
        (ThreeSum.WeightedScore.remaining primes s q nA nB nC a b c s) := by
  exact @ThreeSum.WeightedScore.score_eq_remaining_sourceProof

#print axioms solution
