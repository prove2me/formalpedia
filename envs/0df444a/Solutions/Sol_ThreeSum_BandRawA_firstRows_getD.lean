-- Prove2me | solution 1 for ThreeSum.BandRawA.firstRows_getD
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:38:57.629929+00:00
-- url     : https://prove2.me/submissions/d56a38ef-f196-49d5-869f-204a2dd9cc43

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
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
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
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
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
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
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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








































theorem row_getElem {n g owner j : ℕ} {r : Record} (hj : j < (row n g owner r).length) :
    (row n g owner r)[j]=⟨owner,start g r.a+j⟩ := by
  unfold row at hj ⊢
  split_ifs with hf
  · simp only [List.getElem_map,List.getElem_range]
  · simp [hf] at hj



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





theorem firstRows_getD_sourceProof {n g s i j : ℕ} {rs : List Record}
    (hs : s < i) (hj : j < (row n g s (rs.getD s default)).length) :
    (firstRows n g rs i).getD (count n g rs s+j) default=
      ⟨s,BandPartition.start g (rs.getD s default).a+j⟩ := by
  induction i with
  | zero => omega
  | succ i ih =>
    rw [firstRows_succ]
    by_cases hsi : s < i
    · rw [List.getD_append _ _ _ _ (index_lt_firstRows hsi hj)]
      exact ih hsi
    · have he : s=i := by omega
      subst s
      rw [List.getD_append_right _ _ _ _ (by change count n g rs i ≤ count n g rs i+j; omega)]
      change (row n g i (rs.getD i default)).getD (count n g rs i+j-count n g rs i) default=_
      rw [Nat.add_sub_cancel_left,List.getD_eq_getElem _ _ hj,row_getElem hj]



































































































end ThreeSum.BandRawA

end


theorem solution : ∀ {n g s i j : Nat} {rs : List.{0} ThreeSum.BandCandidateRows.Record},
  @LT.lt.{0} Nat instLTNat s i →
    @LT.lt.{0} Nat instLTNat j
        (@List.length.{0} ThreeSum.BandRawA.Label
          (ThreeSum.BandRawA.row n g s
            (@List.getD.{0} ThreeSum.BandCandidateRows.Record rs s
              (@Inhabited.default.{1} ThreeSum.BandCandidateRows.Record
                ThreeSum.BandCandidateRows.instInhabitedRecord)))) →
      @Eq.{1} ThreeSum.BandRawA.Label
        (@List.getD.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.firstRows n g rs i)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.BandRawA.count n g rs s) j)
          (@Inhabited.default.{1} ThreeSum.BandRawA.Label ThreeSum.BandRawA.instInhabitedLabel))
        { owner := s,
          position :=
            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (ThreeSum.BandPartition.start g
                (@List.getD.{0} ThreeSum.BandCandidateRows.Record rs s
                    (@Inhabited.default.{1} ThreeSum.BandCandidateRows.Record
                      ThreeSum.BandCandidateRows.instInhabitedRecord)).a)
              j } := by
  exact @ThreeSum.BandRawA.firstRows_getD_sourceProof

#print axioms solution
