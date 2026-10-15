-- Prove2me | solution 1 for ThreeSum.BandPrimeChoice.modulus_score_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:42:01.8879+00:00
-- url     : https://prove2.me/submissions/e35d8c49-97b2-43b6-ab0f-51779e94f13f

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_LightMinimum_least_value_le
import Theorems.Thm_ThreeSum_LightPrimeChain_sum_scores_le_log


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandWeightedScore
end ThreeSum.BandWeightedScore
namespace ThreeSum.LightPrimeMinimum
end ThreeSum.LightPrimeMinimum
namespace ThreeSum.WeightedScore
end ThreeSum.WeightedScore

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






















































































































theorem difference_bound {nA nB nC U : ℕ} {A B C : ℕ → ℤ}
    (hA : ∀ i < nA, |A i| ≤ (U : ℤ))
    (hB : ∀ i < nB, |B i| ≤ (U : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (U : ℤ)) :
    ∀ t ∈ ModuloCounts.triples nA nB nC,
      (ModuloCounts.difference A B C t).natAbs ≤ 3*U := by
  intro t ht
  simp only [ModuloCounts.triples,mem_product,mem_range] at ht
  have ha := abs_le.mp (hA _ ht.1)
  have hb := abs_le.mp (hB _ ht.2.1)
  have hc := abs_le.mp (hC _ ht.2.2)
  have hh : |ModuloCounts.difference A B C t| ≤ (3*U : ℤ) := by
    unfold ModuloCounts.difference
    exact abs_le.mpr ⟨by omega,by omega⟩
  rw [← Int.natCast_natAbs] at hh
  exact_mod_cast hh
































variable {lim : Limits} {P : Program} {d : ℕ}














































































































































































































end ThreeSum.LightPrimeChain

end

section


/-!
# The aggregate weighted score of physical band-owner candidates

Each flagged owner contributes the score of its three actual truncated
bands. Owner multiplicities are retained. The contraction and initial bound
therefore apply to the same quadratic catalog that the program scans.
-/

namespace ThreeSum.BandWeightedScore

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000











theorem position_lt {n g a i : ℕ} (hi : i < length n g a) : a*g+i < n := by
  have hh := min_le_right g (n-a*g)
  unfold length at hi
  omega



















































































theorem sum_blocks_le_log (primes : ℕ → ℕ) (s q nA nB nC g y U : ℕ)
    (A B C : ℕ → ℤ) (r : Record) (hy : 1 < y)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j)
    (hlo : ∀ i < s, y ≤ primes i)
    (hA : ∀ i < nA, |A i| ≤ (U : ℤ)) (hB : ∀ i < nB, |B i| ≤ (U : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (U : ℤ)) :
    (∑ i ∈ range s, block primes s (q*primes i) nA nB nC g A B C r) ≤
      Nat.log y (3*U)*block primes s q nA nB nC g A B C r := by
  unfold block
  by_cases hf : r.flag=1
  · simp only [if_pos hf]
    exact LightPrimeChain.sum_scores_le_log primes s q _ _ _ _ _ _ y (3*U) hy hprime hinj hlo
      (LightPrimeChain.difference_bound (fun i hi => hA _ (position_lt hi))
        (fun i hi => hB _ (position_lt hi)) (fun i hi => hC _ (position_lt hi)))
  · simp [hf]

theorem sum_scores_le_log (primes : ℕ → ℕ) (s q nA nB nC g y U : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) (hy : 1 < y)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j)
    (hlo : ∀ i < s, y ≤ primes i)
    (hA : ∀ i < nA, |A i| ≤ (U : ℤ)) (hB : ∀ i < nB, |B i| ≤ (U : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (U : ℤ)) :
    (∑ i ∈ range s, score primes s (q*primes i) nA nB nC g A B C rs) ≤
      Nat.log y (3*U)*score primes s q nA nB nC g A B C rs := by
  unfold score partialScore
  rw [sum_comm,mul_sum]
  exact sum_le_sum fun i _ => sum_blocks_le_log primes s q nA nB nC g y U A B C _
    hy hprime hinj hlo hA hB hC

end ThreeSum.BandWeightedScore

end

section


/-!
# A common contracting modulus for the complete band-owner catalog

The same deterministic first-minimum rule is applied to the sum of every
flagged owner's score. These are joint choices for all bands, rather than
independent moduli whose contractions could not be combined.
-/

namespace ThreeSum.BandPrimeChoice

open BandCandidateRows BandWeightedScore Finset
open scoped BigOperators

set_option maxHeartbeats 1400000
set_option maxRecDepth 8000

















theorem chosenPrime_min (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) {i : ℕ} (hi : i < s) :
    score primes s (q*chosenPrime primes s q nA nB nC g A B C rs) nA nB nC g A B C rs ≤
      score primes s (q*primes i) nA nB nC g A B C rs := by
  have hh := LightMinimum.least_value_le (candidateScore primes s q nA nB nC g A B C rs) s i hi
  dsimp only [candidateScore] at hh
  exact_mod_cast hh

theorem chosenPrime_contracts (primes : ℕ → ℕ) (s q nA nB nC g y U : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) (hy : 1 < y)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j)
    (hlo : ∀ i < s, y ≤ primes i)
    (hA : ∀ i < nA, |A i| ≤ (U : ℤ)) (hB : ∀ i < nB, |B i| ≤ (U : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (U : ℤ)) :
    s*score primes s (q*chosenPrime primes s q nA nB nC g A B C rs) nA nB nC g A B C rs ≤
      Nat.log y (3*U)*score primes s q nA nB nC g A B C rs := by
  calc
    _ = ∑ _i ∈ range s,
        score primes s (q*chosenPrime primes s q nA nB nC g A B C rs) nA nB nC g A B C rs := by simp
    _ ≤ ∑ i ∈ range s, score primes s (q*primes i) nA nB nC g A B C rs :=
      sum_le_sum fun i hi => chosenPrime_min primes s q nA nB nC g A B C rs (mem_range.mp hi)
    _ ≤ _ := sum_scores_le_log primes s q nA nB nC g y U A B C rs hy hprime hinj hlo hA hB hC

































theorem modulus_score_bound_sourceProof (primes : ℕ → ℕ) (s nA nB nC g y U r : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) (hy : 1 < y)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j)
    (hlo : ∀ i < s, y ≤ primes i)
    (hA : ∀ i < nA, |A i| ≤ (U : ℤ)) (hB : ∀ i < nB, |B i| ≤ (U : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (U : ℤ)) :
    s^r*score primes s (modulus primes s nA nB nC g A B C rs r) nA nB nC g A B C rs ≤
      (Nat.log y (3*U))^r*score primes s 1 nA nB nC g A B C rs := by
  induction r with
  | zero => simp [modulus]
  | succ r ih =>
    let q := modulus primes s nA nB nC g A B C rs r
    have hs := chosenPrime_contracts primes s q nA nB nC g y U A B C rs hy hprime hinj hlo hA hB hC
    calc
      _ = s^r*(s*score primes s
          (q*chosenPrime primes s q nA nB nC g A B C rs) nA nB nC g A B C rs) := by
        simp only [modulus,q,pow_succ]
        ring
      _ ≤ s^r*(Nat.log y (3*U)*score primes s q nA nB nC g A B C rs) := Nat.mul_le_mul_left _ hs
      _ = Nat.log y (3*U)*(s^r*score primes s q nA nB nC g A B C rs) := by ring
      _ ≤ Nat.log y (3*U)*((Nat.log y (3*U))^r*score primes s 1 nA nB nC g A B C rs) :=
        Nat.mul_le_mul_left _ ih
      _ = _ := by ring
































end ThreeSum.BandPrimeChoice

end


theorem solution : ∀ (primes : Nat → Nat) (s nA nB nC g y U r : Nat) (A B C : Nat → Int) (rs : List.{0} ThreeSum.BandCandidateRows.Record),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) y →
    (∀ (i : Nat), @LT.lt.{0} Nat instLTNat i s → Nat.Prime (primes i)) →
      (∀ (i : Nat),
          @LT.lt.{0} Nat instLTNat i s →
            ∀ (j : Nat), @LT.lt.{0} Nat instLTNat j s → @Eq.{1} Nat (primes i) (primes j) → @Eq.{1} Nat i j) →
        (∀ (i : Nat), @LT.lt.{0} Nat instLTNat i s → @LE.le.{0} Nat instLENat y (primes i)) →
          (∀ (i : Nat),
              @LT.lt.{0} Nat instLTNat i nA →
                @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (A i))
                  (@Nat.cast.{0} Int instNatCastInt U)) →
            (∀ (i : Nat),
                @LT.lt.{0} Nat instLTNat i nB →
                  @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (B i))
                    (@Nat.cast.{0} Int instNatCastInt U)) →
              (∀ (i : Nat),
                  @LT.lt.{0} Nat instLTNat i nC →
                    @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (C i))
                      (@Nat.cast.{0} Int instNatCastInt U)) →
                @LE.le.{0} Nat instLENat
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) s r)
                    (ThreeSum.BandWeightedScore.score primes s
                      (ThreeSum.BandPrimeChoice.modulus primes s nA nB nC g A B C rs r) nA nB nC g A B C rs))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                      (Nat.log y
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) U))
                      r)
                    (ThreeSum.BandWeightedScore.score primes s
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) nA nB nC g A B C rs)) := by
  exact @ThreeSum.BandPrimeChoice.modulus_score_bound_sourceProof

#print axioms solution
