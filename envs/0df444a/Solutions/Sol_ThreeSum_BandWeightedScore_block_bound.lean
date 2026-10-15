-- Prove2me | solution 1 for ThreeSum.BandWeightedScore.block_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:35:47.740669+00:00
-- url     : https://prove2.me/submissions/87fc471d-4fc7-46ed-9721-41acae611d40

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
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
import Theorems.Thm_ThreeSum_WeightedScore_score_eq_remaining


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.Arithmetic
end ThreeSum.Arithmetic
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.LightResidueHistogram
end ThreeSum.LightResidueHistogram
namespace ThreeSum.ModuloCounts
end ThreeSum.ModuloCounts
namespace ThreeSum.WeightedModuli
end ThreeSum.WeightedModuli

section


/-!
# Modular triple counts from the original integer arrays

This interface identifies the executable histogram/correlation lookup with
the exact `Arithmetic.modCount` used in the weighted false-triple argument.
The three indices retain their multiplicities even when input values repeat.
-/

namespace ThreeSum.ModuloCounts

open Finset LightResidueHistogram
open scoped BigOperators



































theorem count_le (p nA nB nC : ℕ) (a b c : ℕ → ℤ) :
    count p nA nB nC a b c ≤ nA*nB*nC := by
  have h : count p nA nB nC a b c ≤ (triples nA nB nC).card := by
    unfold count Arithmetic.modCount
    calc
      _ ≤ ∑ _t ∈ triples nA nB nC, (1 : ℕ) := by
        apply sum_le_sum
        intro t ht
        unfold Arithmetic.dividesIndicator
        split <;> omega
      _ = _ := by simp
  simpa only [triples, card_product, card_range, Nat.mul_assoc] using h




















end ThreeSum.ModuloCounts

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






























































theorem remaining_le (primes : ℕ → ℕ) (s q nA nB nC : ℕ)
    (a b c : ℕ → ℤ) (i : ℕ) :
    remaining primes s q nA nB nC a b c i ≤ s * (nA*nB*nC) :=
  (Nat.sub_le _ _).trans (Nat.mul_le_mul_left s (count_le q nA nB nC a b c))






























































end ThreeSum.WeightedScore

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



theorem length_le (n g a : ℕ) : length n g a ≤ g := min_le_left _ _










































theorem block_bound_sourceProof (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (r : Record)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j) :
    block primes s q nA nB nC g A B C r ≤ s*g^3 := by
  unfold block
  split_ifs
  · rw [WeightedScore.score_eq_remaining _ _ _ _ _ _ _ _ _ hprime hinj]
    have hh := WeightedScore.remaining_le primes s q (length nA g r.a)
      (length nB g r.b) (length nC g r.c)
      (fun i => A (r.a*g+i)) (fun i => B (r.b*g+i)) (fun i => C (r.c*g+i)) s
    have hp : length nA g r.a*length nB g r.b*length nC g r.c ≤ g^3 := by
      calc
        _ ≤ g*g*g := Nat.mul_le_mul (Nat.mul_le_mul (length_le ..) (length_le ..)) (length_le ..)
        _ = _ := by ring
    exact hh.trans (Nat.mul_le_mul_left s hp)
  · omega


































































end ThreeSum.BandWeightedScore

end


theorem solution : ∀ (primes : Nat → Nat) (s q nA nB nC g : Nat) (A B C : Nat → Int) (r : ThreeSum.BandCandidateRows.Record),
  (∀ (i : Nat), @LT.lt.{0} Nat instLTNat i s → Nat.Prime (primes i)) →
    (∀ (i : Nat),
        @LT.lt.{0} Nat instLTNat i s →
          ∀ (j : Nat), @LT.lt.{0} Nat instLTNat j s → @Eq.{1} Nat (primes i) (primes j) → @Eq.{1} Nat i j) →
      @LE.le.{0} Nat instLENat (ThreeSum.BandWeightedScore.block primes s q nA nB nC g A B C r)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) s
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) g
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) := by
  exact @ThreeSum.BandWeightedScore.block_bound_sourceProof

#print axioms solution
