-- Prove2me | solution 1 for ThreeSum.BandRawA.row_stored
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:39:07.00406+00:00
-- url     : https://prove2.me/submissions/f783e672-ff55-430c-9333-54b336054f61

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
namespace Light
end Light
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































theorem ownerLabels_length (ls : List Label) : (ownerLabels ls).length=ls.length := List.length_map ..
theorem positionLabels_length (ls : List Label) : (positionLabels ls).length=ls.length := List.length_map ..





















































































end ThreeSum.BandRawA

end

section


/-! # The three retained parallel arrays of A-value incidences -/

namespace ThreeSum.BandRawA

open Light BandCandidateRows

set_option maxHeartbeats 1400000































theorem row_stored_sourceProof {μ : ℕ → ℤ} {vals owners positions n g owner : ℕ}
    {r : Record} {f : ℕ → ℤ}
    (H : ∀ j < (row n g owner r).length,
      μ (vals+j)=f (BandPartition.start g r.a+j) ∧ μ (owners+j)=(owner : ℤ) ∧
        μ (positions+j)=((BandPartition.start g r.a+j : ℕ) : ℤ)) :
    Stored μ vals owners positions f (row n g owner r) := by
  constructor
  · intro j hj
    have hj' : j < (row n g owner r).length := by simpa only [values_length] using hj
    dsimp only [values] at hj ⊢
    rw [List.getElem_map,row_getElem hj']
    exact (H j hj').1
  · intro j hj
    have hj' : j < (row n g owner r).length := by simpa only [ownerLabels_length] using hj
    dsimp only [ownerLabels] at hj ⊢
    rw [List.getElem_map,row_getElem hj']
    exact (H j hj').2.1
  · intro j hj
    have hj' : j < (row n g owner r).length := by simpa only [positionLabels_length] using hj
    dsimp only [positionLabels] at hj ⊢
    rw [List.getElem_map,row_getElem hj']
    exact (H j hj').2.2































end ThreeSum.BandRawA

end


theorem solution : ∀ {μ : Nat → Int} {vals owners positions n g owner : Nat} {r : ThreeSum.BandCandidateRows.Record} {f : Nat → Int},
  (∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.row n g owner r)) →
        And
          (@Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) vals j))
            (f
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.BandPartition.start g r.a) j)))
          (And
            (@Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) owners j))
              (@Nat.cast.{0} Int instNatCastInt owner))
            (@Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) positions j))
              (@Nat.cast.{0} Int instNatCastInt
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.BandPartition.start g r.a)
                  j))))) →
    ThreeSum.BandRawA.Stored μ vals owners positions f (ThreeSum.BandRawA.row n g owner r) := by
  exact @ThreeSum.BandRawA.row_stored_sourceProof

#print axioms solution
