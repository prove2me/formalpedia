-- Prove2me | solution 1 for ThreeSum.BandRawA.owner_weightedFalseCount
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:09:19.969999+00:00
-- url     : https://prove2.me/submissions/27fdaa67-534a-4dd4-a7ee-b20c134e383f

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
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
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
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
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_BandRawA_firstRows_getD


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition

section


/-!
# Exact A-value incidences of the physical band-owner catalog

Each successful owner contributes only its A band. Labels retain the
physical owner slot and the coordinate in the retained sorted A array.
Equal values and equal triples in different owner slots remain distinct.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows BandEnumeration BandPartition

set_option maxHeartbeats 1600000
set_option maxRecDepth 7000





























theorem row_length (n g owner : ℕ) (r : Record) :
    (row n g owner r).length=if r.flag=1 then bandLength n g r.a else 0 := by
  unfold row
  split_ifs <;> simp
















theorem firstRows_succ (n g : ℕ) (rs : List Record) (i : ℕ) :
    firstRows n g rs (i+1)=firstRows n g rs i++row n g i (rs.getD i default) := by
  simp only [firstRows,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]



theorem count_succ (n g : ℕ) (rs : List Record) (i : ℕ) :
    count n g rs (i+1)=count n g rs i+(row n g i (rs.getD i default)).length := by
  simp only [count,firstRows_succ,List.length_append]

theorem count_mono (n g : ℕ) (rs : List Record) : Monotone (count n g rs) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [count_succ]
  omega




































































































end ThreeSum.BandRawA

end

section


/-!
# Physical incidence indices and their exact owner coordinates

An incidence at position `count owner + localA` retains that physical
owner and its sorted A coordinate. Every emitted index has exactly this
form, including equal values emitted by different owners.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows

set_option maxHeartbeats 1700000
set_option maxRecDepth 7000










theorem index_lt_firstRows {n g s i j : ℕ} {rs : List Record}
    (hs : s < i) (hj : j < (row n g s (rs.getD s default)).length) :
    count n g rs s+j < (firstRows n g rs i).length := by
  have hm := count_mono n g rs (show s+1 ≤ i by omega)
  rw [count_succ] at hm
  change count n g rs s+j < count n g rs i
  omega

theorem index_lt_items {n g s j : ℕ} {rs : List Record}
    (hs : s < rs.length) (hj : j < (row n g s (rs.getD s default)).length) :
    count n g rs s+j < (items n g rs).length := index_lt_firstRows hs hj


















theorem items_getD {n g s j : ℕ} {rs : List Record}
    (hs : s < rs.length) (hj : j < (row n g s (rs.getD s default)).length) :
    labelAt n g rs (count n g rs s+j)=
      ⟨s,BandPartition.start g (rs.getD s default).a+j⟩ := firstRows_getD hs hj































































theorem values_getD {n g k : ℕ} {rs : List Record} (f : ℕ → ℤ)
    (hk : k < (items n g rs).length) :
    (values f (items n g rs)).getD k 0=f (labelAt n g rs k).position := by
  unfold values labelAt
  rw [List.getD_map_of_lt _ hk default 0]

theorem values_getD_owner {n g s j : ℕ} {rs : List Record} (f : ℕ → ℤ)
    (hs : s < rs.length) (hj : j < (row n g s (rs.getD s default)).length) :
    (values f (items n g rs)).getD (count n g rs s+j) 0=
      f (BandPartition.start g (rs.getD s default).a+j) := by
  rw [values_getD f (index_lt_items hs hj),items_getD hs hj]




















end ThreeSum.BandRawA

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





theorem length_eq_partition (n g a : ℕ) :
    length n g a=BandPartition.stop n g a-BandPartition.start g a := by
  unfold length BandPartition.stop BandPartition.start
  rw [Nat.add_mul,Nat.one_mul]
  omega























































































































end ThreeSum.BandWeightedScore

end

section


/-!
# Each physical A incidence retains exactly its owner's B/C product

The products in this file are mathematical counting domains. The actual
catalog is still constructed by the verified quadratic owner loop and
linear band copies. Distinct owner products are disjoint because their
physical A incidence indices differ, even when their values coincide.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 1900000
set_option maxRecDepth 8000














theorem bandLength_eq_score_length (n g a : ℕ) :
    bandLength n g a=BandWeightedScore.length n g a :=
  (BandWeightedScore.length_eq_partition n g a).symm













































































theorem sum_aIndices (F : ℕ → ℕ) (n g : ℕ) (rs : List Record) (s : ℕ) :
    (∑ k ∈ aIndices n g rs s, F k)=
      ∑ j ∈ range (row n g s (rs.getD s default)).length, F (count n g rs s+j) := by
  unfold aIndices
  exact sum_image (fun i _ j _ he => by omega)

theorem sum_bandPositions (F : ℕ → ℕ) (n g a : ℕ) :
    (∑ p ∈ bandPositions n g a, F p)=
      ∑ j ∈ range (bandLength n g a), F (BandPartition.start g a+j) := by
  unfold bandPositions
  exact sum_image (fun i _ j _ he => by omega)

theorem sum_ownerProduct (F : (ℕ × ℕ × ℕ) → ℕ) (nA nB nC g : ℕ)
    (rs : List Record) (s : ℕ) :
    (∑ t ∈ ownerProduct nA nB nC g rs s, F t)=
      ∑ i ∈ range (row nA g s (rs.getD s default)).length,
        ∑ j ∈ range (bandLength nB g (rs.getD s default).b),
          ∑ k ∈ range (bandLength nC g (rs.getD s default).c),
            F (count nA g rs s+i,
              BandPartition.start g (rs.getD s default).b+j,
              BandPartition.start g (rs.getD s default).c+k) := by
  rw [ownerProduct,sum_product,sum_aIndices]
  apply sum_congr rfl
  intro i hi
  rw [sum_product,sum_bandPositions]
  apply sum_congr rfl
  intro j hj
  exact sum_bandPositions _ _ _ _






































end ThreeSum.BandRawA

end

section


/-!
# The aggregate prime score is the exact physical incidence-product score

The executable A catalog supplies the first-coordinate values. Its owner
metadata supplies the B/C slices. Thus the mathematical score summed by
the actual prime selector counts this same domain with all multiplicities.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 1900000
set_option maxRecDepth 8000




theorem valueAt_owner {n g s j : ℕ} {rs : List Record} (A : ℕ → ℤ)
    (hs : s < rs.length) (hj : j < (row n g s (rs.getD s default)).length) :
    valueAt n g rs A (count n g rs s+j)=A (BandPartition.start g (rs.getD s default).a+j) :=
  values_getD_owner A hs hj

theorem owner_weightedFalseCount_sourceProof (primes : ℕ → ℕ) (aux q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) {s : ℕ} (hs : s < rs.length) :
    Arithmetic.weightedFalseCount (ownerProduct nA nB nC g rs s)
      (ModuloCounts.difference (valueAt nA g rs A) B C)
      (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux)) q=
      BandWeightedScore.block primes aux q nA nB nC g A B C (rs.getD s default) := by
  unfold Arithmetic.weightedFalseCount
  rw [sum_ownerProduct]
  unfold BandWeightedScore.block
  by_cases hf : (rs.getD s default).flag=1
  · simp only [if_pos hf,WeightedScore.score,Arithmetic.weightedFalseCount,
      ModuloCounts.triples,sum_product]
    have hrow : (row nA g s (rs.getD s default)).length=
        BandWeightedScore.length nA g (rs.getD s default).a := by
      rw [row_length,if_pos hf,bandLength_eq_score_length]
    rw [hrow]
    simp_rw [bandLength_eq_score_length]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    apply sum_congr rfl
    intro k hk
    have hi' : i < (row nA g s (rs.getD s default)).length := by
      rw [hrow]
      exact mem_range.mp hi
    simp only [ModuloCounts.difference,valueAt_owner A hs hi',BandPartition.start]
    rfl
  · simp only [if_neg hf,row_length,range_zero,sum_empty]



























































end ThreeSum.BandRawA

end


theorem solution : ∀ (primes : Nat → Nat) (aux q nA nB nC g : Nat) (A B C : Nat → Int) (rs : List.{0} ThreeSum.BandCandidateRows.Record)
  {s : Nat},
  @LT.lt.{0} Nat instLTNat s (@List.length.{0} ThreeSum.BandCandidateRows.Record rs) →
    @Eq.{1} Nat
      (@ThreeSum.Arithmetic.weightedFalseCount.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))
        (ThreeSum.BandRawA.ownerProduct nA nB nC g rs s)
        (ThreeSum.ModuloCounts.difference (ThreeSum.BandRawA.valueAt nA g rs A) B C)
        (ThreeSum.Auxiliary.moduli (ThreeSum.WeightedScore.auxiliarySet primes aux))
        (@Nat.cast.{0} Int instNatCastInt q))
      (ThreeSum.BandWeightedScore.block primes aux q nA nB nC g A B C
        (@List.getD.{0} ThreeSum.BandCandidateRows.Record rs s
          (@Inhabited.default.{1} ThreeSum.BandCandidateRows.Record ThreeSum.BandCandidateRows.instInhabitedRecord))) := by
  exact @ThreeSum.BandRawA.owner_weightedFalseCount_sourceProof

#print axioms solution
