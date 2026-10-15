-- Prove2me | solution 1 for ThreeSum.BandRawA.mem_aIndices_iff_owner
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:09:19.202036+00:00
-- url     : https://prove2.me/submissions/2e21ed4b-e24a-40fb-9b57-f274a05f2db2

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
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















































@[simp] theorem firstRows_zero (n g : ℕ) (rs : List Record) : firstRows n g rs 0=[] := rfl

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

theorem firstRows_index {n g i k : ℕ} {rs : List Record}
    (hk : k < (firstRows n g rs i).length) :
    ∃ s < i, ∃ j < (row n g s (rs.getD s default)).length,
      k=count n g rs s+j := by
  induction i with
  | zero => simp at hk
  | succ i ih =>
    by_cases hki : k < (firstRows n g rs i).length
    · obtain ⟨s,hs,j,hj,he⟩ := ih hki
      exact ⟨s,by omega,j,hj,he⟩
    · have hlen : (firstRows n g rs (i+1)).length=
          count n g rs i+(row n g i (rs.getD i default)).length := by
        rw [firstRows_succ,List.length_append]
        rfl
      rw [hlen] at hk
      change ¬ k < count n g rs i at hki
      exact ⟨i,by omega,k-count n g rs i,by omega,by omega⟩

theorem items_index {n g k : ℕ} {rs : List Record}
    (hk : k < (items n g rs).length) :
    ∃ s < rs.length, ∃ j < (row n g s (rs.getD s default)).length,
      k=count n g rs s+j := firstRows_index hk







































































end ThreeSum.BandRawA

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


















theorem mem_aIndices {n g s k : ℕ} {rs : List Record} :
    k ∈ aIndices n g rs s ↔
      ∃ j < (row n g s (rs.getD s default)).length, k=count n g rs s+j := by
  constructor
  · intro hk
    obtain ⟨j,hj,he⟩ := mem_image.mp hk
    exact ⟨j,mem_range.mp hj,he.symm⟩
  · rintro ⟨j,hj,he⟩
    exact mem_image.mpr ⟨j,mem_range.mpr hj,he.symm⟩

theorem mem_aIndices_iff_owner_sourceProof {n g s k : ℕ} {rs : List Record} (hs : s < rs.length) :
    k ∈ aIndices n g rs s ↔
      k < (items n g rs).length ∧ (labelAt n g rs k).owner=s := by
  constructor
  · intro hk
    obtain ⟨j,hj,rfl⟩ := mem_aIndices.mp hk
    exact ⟨index_lt_items hs hj,by rw [items_getD hs hj]⟩
  · rintro ⟨hk,ho⟩
    obtain ⟨t,ht,j,hj,he⟩ := items_index hk
    have heLabel := items_getD ht hj
    rw [← he] at heLabel
    have hts : t=s := by simpa only [heLabel] using ho
    subst t
    exact mem_aIndices.mpr ⟨j,hj,he⟩






















































































































end ThreeSum.BandRawA

end


theorem solution : ∀ {n g s k : Nat} {rs : List.{0} ThreeSum.BandCandidateRows.Record}
  (hs : @LT.lt.{0} Nat instLTNat s (@List.length.{0} ThreeSum.BandCandidateRows.Record rs)),
  Iff
    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (ThreeSum.BandRawA.aIndices n g rs s) k)
    (And (@LT.lt.{0} Nat instLTNat k (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)))
      (@Eq.{1} Nat (ThreeSum.BandRawA.labelAt n g rs k).owner s)) := by
  exact @ThreeSum.BandRawA.mem_aIndices_iff_owner_sourceProof

#print axioms solution
