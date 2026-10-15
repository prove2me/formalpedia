-- Prove2me | solution 1 for ThreeSum.LightPrimeChain.sum_scores_le_log
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:21:05.213758+00:00
-- url     : https://prove2.me/submissions/01cceed3-94ee-4cbb-8b38-cc28f40ef0dd

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
import Theorems.Thm_ThreeSum_PrimeChain_prime_divisors_card_le_log
import Theorems.Thm_ThreeSum_PrimeChain_sum_scores_le


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightPrimeMinimum
end ThreeSum.LightPrimeMinimum
namespace ThreeSum.WeightedScore
end ThreeSum.WeightedScore

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















































































































@[simp] theorem missWeight_zero (L : Finset ℤ) : missWeight L 0 = 0 := by
  simp [missWeight]






























/-! ## Exact early YES from per-original-triple representation caps -/



































































end ThreeSum.Arithmetic

end

section


/-! # Exact deterministic contraction of the weighted modular score -/

namespace ThreeSum.PrimeChain

open Finset
open scoped BigOperators

variable {ι : Type*}




theorem score_eq_weightedFalseCount (T : Finset ι) (difference : ι → ℤ)
    (L : Finset ℤ) (q : ℕ) :
    score T difference (Arithmetic.missWeight L) q =
      Arithmetic.weightedFalseCount T difference L (q : ℤ) := by
  simp only [score, Arithmetic.weightedFalseCount, Int.natCast_dvd]




























































theorem sum_scores_le_log (T : Finset ι) (difference : ι → ℤ) (weight : ℤ → ℕ)
    (hzero : weight 0 = 0) (C : Finset ℕ) (q y M : ℕ) (hy : 1 < y)
    (hprime : ∀ p ∈ C, Nat.Prime p) (hmin : ∀ p ∈ C, y ≤ p)
    (hbound : ∀ i ∈ T, (difference i).natAbs ≤ M) :
    (∑ p ∈ C, score T difference weight (q * p)) ≤
      Nat.log y M * score T difference weight q := by
  apply sum_scores_le T difference weight hzero C q (Nat.log y M)
  intro i hi hz
  exact (prime_divisors_card_le_log C y hy hprime hmin (difference i) hz).trans
    (Nat.log_mono_right (hbound i hi))























































































end ThreeSum.PrimeChain

end

section


/-!
# Executing a deterministic chain of contracting moduli

Each level runs the concrete prime-score minimum program and multiplies the
current modulus by its returned prime. The exact finite contraction theorem
applies to this executed choice, with all original triple multiplicities.
-/

namespace ThreeSum.LightPrimeChain

open Light WeightedScore LightPrimeMinimum Finset
open scoped BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000










































/-- Convert the finite-prime averaging theorem to the actual array order. -/
theorem sum_scores_le_log_sourceProof (primes : ℕ → ℕ) (s q nA nB nC : ℕ)
    (A B C : ℕ → ℤ) (y M : ℕ) (hy : 1 < y)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j)
    (hlo : ∀ i < s, y ≤ primes i)
    (hbound : ∀ t ∈ ModuloCounts.triples nA nB nC,
      (ModuloCounts.difference A B C t).natAbs ≤ M) :
    (∑ i ∈ range s, score primes s (q*primes i) nA nB nC A B C) ≤
      Nat.log y M * score primes s q nA nB nC A B C := by
  let pool := auxiliarySet primes s
  have hpr : ∀ p ∈ pool, Nat.Prime p := by
    intro p hp
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
    exact hprime i (mem_range.mp hi)
  have hlow : ∀ p ∈ pool, y ≤ p := by
    intro p hp
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
    exact hlo i (mem_range.mp hi)
  have hsum : (∑ i ∈ range s, score primes s (q*primes i) nA nB nC A B C) =
      ∑ p ∈ pool, score primes s (q*p) nA nB nC A B C := by
    symm
    unfold pool auxiliarySet
    rw [sum_image]
    intro i hi j hj heq
    exact hinj i (mem_range.mp hi) j (mem_range.mp hj) heq
  rw [hsum]
  have havg := PrimeChain.sum_scores_le_log (ModuloCounts.triples nA nB nC)
    (ModuloCounts.difference A B C) (Arithmetic.missWeight (Auxiliary.moduli pool))
    (Arithmetic.missWeight_zero _) pool q y M hy hpr hlow hbound
  simpa only [PrimeChain.score_eq_weightedFalseCount,score,pool] using havg





























































































variable {lim : Limits} {P : Program} {d : ℕ}














































































































































































































end ThreeSum.LightPrimeChain

end


theorem solution : ∀ (primes : Nat → Nat) (s q nA nB nC : Nat) (A B C : Nat → Int) (y M : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) y →
    (∀ (i : Nat), @LT.lt.{0} Nat instLTNat i s → Nat.Prime (primes i)) →
      (∀ (i : Nat),
          @LT.lt.{0} Nat instLTNat i s →
            ∀ (j : Nat), @LT.lt.{0} Nat instLTNat j s → @Eq.{1} Nat (primes i) (primes j) → @Eq.{1} Nat i j) →
        (∀ (i : Nat), @LT.lt.{0} Nat instLTNat i s → @LE.le.{0} Nat instLENat y (primes i)) →
          (∀ (t : Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)),
              @Membership.mem.{0, 0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))
                  (Finset.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)))
                  (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)))
                    (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))
                    (@Finset.instSetLike.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))))
                  (ThreeSum.ModuloCounts.triples nA nB nC) t →
                @LE.le.{0} Nat instLENat (ThreeSum.ModuloCounts.difference A B C t).natAbs M) →
            @LE.le.{0} Nat instLENat
              (∑ i ∈ Finset.range s,
                ThreeSum.WeightedScore.score primes s
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q (primes i)) nA nB nC A B C)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (Nat.log y M)
                (ThreeSum.WeightedScore.score primes s q nA nB nC A B C)) := by
  exact @ThreeSum.LightPrimeChain.sum_scores_le_log_sourceProof

#print axioms solution
