-- Prove2me | solution 1 for ThreeSum.BandCandidateRows.mem_records_owner
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:37:43.952913+00:00
-- url     : https://prove2.me/submissions/d6dd6d63-ea8b-43b8-a8dc-f84483841971

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
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
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
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
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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
import Mathlib.Tactic.Tauto


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration

section


/-! # List and memory interfaces for the exact candidate record array -/

namespace ThreeSum.BandCandidateRows

open Light BandEnumeration

set_option maxHeartbeats 1300000

theorem mem_records_owner_sourceProof {A B C : Family} {r : Record} (hr : r ∈ records A B C) :
    ∃ o : Owner A B C, fromOwner A B C o=r := by
  rcases List.mem_append.mp hr with hb | hh
  · obtain ⟨j,hj,hk⟩ := List.mem_flatMap.mp hb
    obtain ⟨k,hk,he⟩ := List.mem_map.mp hk
    exact ⟨.inl (⟨j,List.mem_range.mp hj⟩,⟨k,List.mem_range.mp hk⟩),he⟩
  · rcases List.mem_append.mp hh with hb | hc
    · obtain ⟨i,hi,hj⟩ := List.mem_flatMap.mp hb
      obtain ⟨j,hj,he⟩ := List.mem_map.mp hj
      exact ⟨.inr (⟨i,List.mem_range.mp hi⟩,.inl ⟨j,List.mem_range.mp hj⟩),he⟩
    · obtain ⟨i,hi,hk⟩ := List.mem_flatMap.mp hc
      obtain ⟨k,hk,he⟩ := List.mem_map.mp hk
      exact ⟨.inr (⟨i,List.mem_range.mp hi⟩,.inr ⟨k,List.mem_range.mp hk⟩),he⟩



































































end ThreeSum.BandCandidateRows

end


theorem solution : ∀ {A B C : ThreeSum.BandEnumeration.Family} {r : ThreeSum.BandCandidateRows.Record},
  @Membership.mem.{0, 0} ThreeSum.BandCandidateRows.Record (List.{0} ThreeSum.BandCandidateRows.Record)
      (@List.instMembership.{0} ThreeSum.BandCandidateRows.Record) (ThreeSum.BandCandidateRows.records A B C) r →
    ∃ (o : ThreeSum.BandEnumeration.Owner A B C),
      @Eq.{1} ThreeSum.BandCandidateRows.Record (ThreeSum.BandCandidateRows.fromOwner A B C o) r := by
  exact @ThreeSum.BandCandidateRows.mem_records_owner_sourceProof

#print axioms solution
