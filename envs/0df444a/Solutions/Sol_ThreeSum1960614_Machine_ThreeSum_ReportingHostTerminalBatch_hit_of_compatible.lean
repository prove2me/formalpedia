-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.hit_of_compatible
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:01:13.107714+00:00
-- url     : https://prove2.me/submissions/94ca5c29-2acc-4b78-8c81-5c8caa6decf6

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
import Definitions.Def_ThreeSum1960614_Machine_Bundle025
import Definitions.Def_ThreeSum1960614_Machine_Bundle026
import Definitions.Def_ThreeSum1960614_Machine_Bundle027
import Definitions.Def_ThreeSum1960614_Machine_Bundle028
import Definitions.Def_ThreeSum1960614_Machine_Bundle029
import Definitions.Def_ThreeSum1960614_Machine_Bundle030
import Definitions.Def_ThreeSum1960614_Machine_Bundle031
import Definitions.Def_ThreeSum1960614_Machine_Bundle032
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_ReportingHostTerminalChoices_mem_choices
import Theorems.Thm_ThreeSum_BlockForced_forced_disjoint
import Theorems.Thm_ThreeSum_BlockForced_forced_union

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightReportingTerminalMasks
end ThreeSum.LightReportingTerminalMasks
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostTerminalBatch
end ThreeSum.ReportingHostTerminalBatch
namespace ThreeSum.ReportingHostTerminalChoices
end ThreeSum.ReportingHostTerminalChoices
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockForced
end ThreeSum1960614.Machine.ThreeSum.BlockForced
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
end ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
end ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalGraph
end ThreeSum1960614.Machine.ThreeSum.LocalGraph
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
end ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest
end ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch
end ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices
end ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

namespace ThreeSum1960614.Machine

/-!
# Flattening a block family of subsets

The coordinates retain the block index explicitly. Joining and slicing are
mutually inverse, preserve Boolean set operations, and give exact cardinalities
for balanced full inputs and forced prefixes.
-/

namespace ThreeSum.BlockRows
open _root_.ThreeSum.BlockRows


open _root_.Finset
open scoped _root_.BigOperators









@[simp] theorem mem_join {J L : ℕ} {I : Finset (Fin J)}
    {u : Fin J → Finset (Fin L)} {i : Fin J} {x : Fin L} :
    Sigma.mk i x ∈ _root_.ThreeSum.BlockRows.join I u ↔ i ∈ I ∧ x ∈ u i := Finset.mem_sigma

@[simp] theorem mem_flat {J L : ℕ} {u : Fin J → Finset (Fin L)}
    {i : Fin J} {x : Fin L} : Sigma.mk i x ∈ _root_.ThreeSum.BlockRows.flat u ↔ x ∈ u i := by
  simp only [_root_.ThreeSum.BlockRows.flat, _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join, Finset.mem_univ, true_and]



@[simp] theorem row_flat {J L : ℕ} (u : Fin J → Finset (Fin L)) (i : Fin J) :
    _root_.ThreeSum.BlockRows.row (_root_.ThreeSum.BlockRows.flat u) i = u i := by ext x; simp





theorem row_subset {J L : ℕ} {S T : Finset (_root_.ThreeSum.BlockRows.Coord J L)} (h : S ⊆ T) (i : Fin J) :
    _root_.ThreeSum.BlockRows.row S i ⊆ _root_.ThreeSum.BlockRows.row T i := by
  intro x hx
  exact _root_.ThreeSum.BlockRows.mem_row.mpr (h (_root_.ThreeSum.BlockRows.mem_row.mp hx))









theorem join_union_compl {J L : ℕ} (I : Finset (Fin J)) (u : Fin J → Finset (Fin L)) :
    _root_.ThreeSum.BlockRows.join I u ∪ _root_.ThreeSum.BlockRows.join Iᶜ u = _root_.ThreeSum.BlockRows.flat u := by
  ext ⟨i, x⟩
  simp only [Finset.mem_union, _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join, Finset.mem_compl, _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_flat]
  tauto





theorem join_card {J L : ℕ} (I : Finset (Fin J)) (u : Fin J → Finset (Fin L)) :
    (_root_.ThreeSum.BlockRows.join I u).card = ∑ i ∈ I, (u i).card := Finset.card_sigma _ _

theorem join_card_of_balance {J L h : ℕ} (I : Finset (Fin J))
    (u : Fin J → Finset (Fin L)) (hu : ∀ i ∈ I, (u i).card = h) :
    (_root_.ThreeSum.BlockRows.join I u).card = I.card * h := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_card]
  simp only [Finset.sum_congr rfl hu, Finset.sum_const, Nat.nsmul_eq_mul]







@[simp] theorem mem_prefixIndices {J k : ℕ} {i : Fin J} :
    i ∈ _root_.ThreeSum.BlockRows.prefixIndices J k ↔ i.val < k := by simp [_root_.ThreeSum.BlockRows.prefixIndices]



end ThreeSum.BlockRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Concrete retained choices and the global radix encoding

The local choice type retains the occurrence of a map in the deterministic
schedule.  Repeated chosen maps therefore keep their representation
multiplicity.  Canonical integer lifts of their one-hot coefficients feed
the radix recursion, whose coverage and cap are instantiated here with no
local-cover assumptions.
-/

namespace ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalEncoding


set_option maxRecDepth 8000

open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments






















theorem retained_survives {h : ℕ} (c : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h) :
    _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Survives h (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.occurrence c) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge c) := c.property





































































end ThreeSum.GlobalEncoding

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Costed signed residue conversion

This loop uses the benchmark's proved division-free remainder procedure.
Its sign argument supports either an ordinary histogram or a histogram of
the negated original integers. All source multiplicities are retained.
The logarithmic scratch region is reused for each input element.
-/

namespace ThreeSum.LightResidues
open _root_.ThreeSum.LightResidues


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



theorem residue_cast {p : ℕ} (hp : 0 < p) (c x : ℤ) :
    (_root_.ThreeSum.LightResidues.residue p c x : ℤ) = (c * x) % (p : ℤ) := by
  apply Int.toNat_of_nonneg
  exact Int.emod_nonneg _ (by exact_mod_cast hp.ne')

















end ThreeSum.LightResidues

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Query-coordinate lists and weighted subset semantics

The coordinate list has one entry per set bit of the query. Its powers
form a compact weight table for the output-sensitive enumeration routine.
-/

namespace ThreeSum.QueryCoordinates
open _root_.ThreeSum.QueryCoordinates


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open scoped _root_.BigOperators















@[simp] theorem positions_length {W : ℕ} (Q : Finset (Fin W)) :
    (_root_.ThreeSum.QueryCoordinates.positions Q W).length = Q.card := by
  rw [← List.toFinset_card_of_nodup (_root_.ThreeSum.QueryCoordinates.positions_nodup Q W),_root_.ThreeSum.QueryCoordinates.positions_toFinset,_root_.ThreeSum.SubsetAddress.natPositions_card]



















@[simp] theorem setLayer_length (xs : List ℕ) (k : ℕ) :
    (_root_.ThreeSum.QueryCoordinates.setLayer xs k).length = xs.length.choose k := by
  simp [_root_.ThreeSum.QueryCoordinates.setLayer,List.length_sublistsLen]























@[simp] theorem missingSets_length {W : ℕ} (Q : Finset (Fin W)) (k : ℕ) :
    (_root_.ThreeSum.QueryCoordinates.missingSets Q k).length = Q.card.choose k := by
  simp [_root_.ThreeSum.QueryCoordinates.missingSets]



end ThreeSum.QueryCoordinates

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Independent trimmed endpoint histograms on the flattened block ground set

A histogram only inspects one endpoint and the occurrence vector. Its support
is exactly on independently retained balanced block subsets. Compatible
opposite endpoints reconstruct an actual retained choice tuple.
-/

namespace ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockEncoding


set_option maxRecDepth 8000

open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows











@[simp] theorem row_leftSubset {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) (i : Fin J) :
    _root_.ThreeSum.BlockRows.row (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset t) i = (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge (t i)).val.1 := _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.row_flat _ _

@[simp] theorem row_rightSubset {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) (i : Fin J) :
    _root_.ThreeSum.BlockRows.row (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightSubset t) i = (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge (t i)).val.2 := _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.row_flat _ _

@[simp] theorem row_outputSubset {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (i : Fin J) :
    _root_.ThreeSum.BlockRows.row (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputSubset q) i = (q i).2.val := _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.row_flat _ _







theorem leftSubset_disjoint_right {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) :
    Disjoint (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset t) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightSubset t) := by
  apply Finset.disjoint_left.mpr
  intro ⟨i, x⟩ hL hR
  exact Finset.disjoint_left.mp (_root_.ThreeSum.LocalGraph.edge_data (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge (t i))).2.2
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_flat.mp hL) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_flat.mp hR)

theorem leftSubset_union_right {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset t ∪ _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightSubset t = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputSubset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput t) := by
  ext ⟨i, x⟩
  simp only [Finset.mem_union, _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset, _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightSubset, _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputSubset, _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_flat,
    _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput, _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.blockOfChoice, _root_.ThreeSum.LocalGraph.output]

theorem rightSubset_eq_sdiff {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightSubset t = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputSubset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput t) \ _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset t := by
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset_union_right]
  have hd := Finset.disjoint_left.mp (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset_disjoint_right t)
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  aesop















section

private theorem private_a829934bec_positionalHash_map {α β : Type*} (p : ℤ) (f : α → β) (g : β → ℤ)
    (xs : List α) : _root_.ThreeSum.Radix.positionalHash p g (xs.map f) =
      _root_.ThreeSum.Radix.positionalHash p (fun a => g (f a)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, _root_.ThreeSum.Radix.positionalHash, ih]
end


theorem leftAllowed_choice {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (hq : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput t = q) : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.LeftAllowed (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset t) := by
  intro i
  have ho : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.occurrence (t i) = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q i := congrArg (fun q => (q i).1) hq
  refine ⟨by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.row_leftSubset] using (_root_.ThreeSum.LocalGraph.edge_data (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge (t i))).1, ?_⟩
  have hs := (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.retained_survives (t i)).1
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.row_leftSubset, _root_.ThreeSum.LocalGraph.left, ho] using hs

theorem rightAllowed_choice {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (hq : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput t = q) : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.RightAllowed (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightSubset t) := by
  intro i
  have ho : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.occurrence (t i) = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q i := congrArg (fun q => (q i).1) hq
  refine ⟨by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.row_rightSubset] using (_root_.ThreeSum.LocalGraph.edge_data (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge (t i))).2.1, ?_⟩
  have hs := (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.retained_survives (t i)).2
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.row_rightSubset, _root_.ThreeSum.LocalGraph.right, ho] using hs

theorem endpointLeft_choice {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (hq : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput t = q) : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointLeft (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset t) = _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleLeft t := by
  have hl : (List.ofFn fun i => _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q i))
      (_root_.ThreeSum.LocalGraph.leftWord (_root_.ThreeSum.BlockRows.row (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset t) i))) = (List.ofFn t).map _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    have ho : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.occurrence (t i) = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q i := congrArg (fun q => (q i).1) hq
    simp only [Function.comp_apply, _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.row_leftSubset, _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft, _root_.ThreeSum.LocalGraph.left, ho]
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointLeft, hl, _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.private_a829934bec_positionalHash_map]
  rfl

theorem endpointRight_choice {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (hq : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput t = q) : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointRight (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightSubset t) = _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleRight t := by
  have hl : (List.ofFn fun i => _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q i))
      (_root_.ThreeSum.LocalGraph.rightWord (_root_.ThreeSum.BlockRows.row (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightSubset t) i))) = (List.ofFn t).map _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    have ho : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.occurrence (t i) = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q i := congrArg (fun q => (q i).1) hq
    simp only [Function.comp_apply, _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.row_rightSubset, _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight, _root_.ThreeSum.LocalGraph.right, ho]
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointRight, hl, _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.private_a829934bec_positionalHash_map]
  rfl









section Histograms

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]













end Histograms

end ThreeSum.BlockEncoding

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original-input residue keys with a carry offset

The source histogram uses `(x % p + shift) % m`, with two independently
chosen moduli. This procedure computes both remainders from each original
signed input and retains every incidence, including duplicate values.
-/

namespace ThreeSum.LightSourceResidues
open _root_.ThreeSum.LightSourceResidues


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000



theorem key_cast {p m : ℕ} (hm : 0 < m) (shift x : ℤ) :
    (_root_.ThreeSum.LightSourceResidues.key p m shift x : ℤ) = (x % (p : ℤ) + shift) % (m : ℤ) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hm.ne'))













variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}











end ThreeSum.LightSourceResidues

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual forced-prefix endpoint decompositions

Fixing completed blocks partitions each full retained tuple into its fixed
left/right subsets and its remaining left subset. The reconstruction is a
bijection, which identifies every prefix bucket sum with the subset formula.
-/

namespace ThreeSum.BlockForced
open _root_.ThreeSum.BlockForced


set_option maxRecDepth 8000

open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding

section FiniteRows

variable {J L : ℕ}



















theorem forced_left_of_agreement (I : Finset (Fin J)) (u v : Fin J → Finset (Fin L))
    (hv : ∀ i ∈ I, v i = u i) :
    _root_.ThreeSum.BlockForced.prefixLeft I u ∪ _root_.ThreeSum.BlockRows.join Iᶜ v = _root_.ThreeSum.BlockRows.flat v := by
  have he : _root_.ThreeSum.BlockRows.join I u = _root_.ThreeSum.BlockRows.join I v := by
    ext ⟨i, a⟩
    by_cases hi : i ∈ I
    · simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join, hi, true_and, hv i hi]
    · simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join, hi, false_and]
  rw [_root_.ThreeSum.BlockForced.prefixLeft, he]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_union_compl I v

section

private theorem private_92cb238d05_sdiff_of_disjoint_union {S V Q : Finset (_root_.ThreeSum.BlockRows.Coord J L)}
    (hd : Disjoint S V) (hu : S ∪ V = Q) : V = Q \ S := by
  rw [← hu]
  have hd' := Finset.disjoint_left.mp hd
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  aesop
end


end FiniteRows







theorem residual_subset {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (I : Finset (Fin J))
    (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) (hq : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput t = q) : _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.residual I t ⊆ _root_.ThreeSum.BlockForced.remaining I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) := by
  have hL : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset t ⊆ _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputSubset q := by
    rw [← hq, ← _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset_union_right]
    exact Finset.subset_union_left
  intro ⟨i, a⟩ hx
  obtain ⟨hi, ha⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join.mp hx
  apply _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join.mpr
  refine ⟨hi, ?_⟩
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.row_subset hL i
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.row_leftSubset, _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.row_outputSubset] at hh
  exact hh ha

theorem forced_left_completion {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (464 * h))) (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J)
    (ht : t ∈ _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.completedTuples q I u) : _root_.ThreeSum.BlockForced.prefixLeft I u ∪ _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.residual I t = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset t :=
  _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.forced_left_of_agreement I u _ (Finset.mem_filter.mp ht).2.2

theorem forced_right_completion {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (464 * h)))
    (hu : ∀ i ∈ I, u i ⊆ _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q i) (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J)
    (ht : t ∈ _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.completedTuples q I u) :
    _root_.ThreeSum.BlockForced.prefixRight I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) u ∪ (_root_.ThreeSum.BlockForced.remaining I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) \ _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.residual I t) =
      _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightSubset t := by
  have hq := (Finset.mem_filter.mp ht).2.1
  have hx := _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.residual_subset q I t hq
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.private_92cb238d05_sdiff_of_disjoint_union (_root_.ThreeSum.BlockForced.forced_disjoint I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) u (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.residual I t) hx)
    (_root_.ThreeSum.BlockForced.forced_union I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) u hu (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.residual I t) hx)
  rw [he, _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.forced_left_completion q I u t ht, _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightSubset_eq_sdiff, hq]
  rfl









section WeightedCounts

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]







end WeightedCounts

end ThreeSum.BlockForced

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Explicit row-major encoding of the block ground set

Block coordinates are numbered by `block * width + coordinate`. The
equivalence connects compact machine-mask tables on `Fin (J*L)` with the
sigma-typed block sets in the reporting proof. Flattened one-hot coefficients
already include their positional radix factors.
-/

namespace ThreeSum.BlockIndex
open _root_.ThreeSum.BlockIndex


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open scoped _root_.BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false











@[simp] theorem indexSet_card {J L : ℕ} (S : Finset (_root_.ThreeSum.BlockRows.Coord J L)) :
    (_root_.ThreeSum.BlockIndex.indexSet S).card = S.card := Finset.card_map _























end ThreeSum.BlockIndex

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact stored-subset queries for the concrete reporting tree

A malformed prefix has zero mass. Every valid prefix is evaluated by the
stored suffix-zeta stages and the signed subset formula. These values are
proved to equal the natural raw-incidence fiber counts at every tree node.
-/

namespace ThreeSum.StoredReporting
open _root_.ThreeSum.StoredReporting


set_option maxRecDepth 8000

open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced

section

private theorem private_4ccb502193_ofFn_take_eq_iff {α : Type*} {J k : ℕ} (f g : Fin J → α) :
    (List.ofFn f).take k = (List.ofFn g).take k ↔ ∀ i : Fin J, i.val < k → f i = g i := by
  constructor
  · intro he i hi
    have hh := congrArg (fun xs => xs[i.val]?) he
    simpa only [List.getElem?_take_of_lt hi, List.getElem?_ofFn, dif_pos i.isLt,
      Option.some.injEq] using hh
  · intro h
    apply List.ext_getElem?
    intro i
    by_cases hi : i < k
    · rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt hi]
      by_cases hiJ : i < J
      · simp only [List.getElem?_ofFn, dif_pos hiJ, h ⟨i, hiJ⟩ hi]
      · simp only [List.getElem?_ofFn, dif_neg hiJ]
    · simp only [List.getElem?_take, hi, ite_false]
end






theorem take_prefixRows {J L k : ℕ} (pre : List (Finset (Fin L)))
    (hp : pre.length = k) (hk : k ≤ J) : (List.ofFn (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre)).take k = pre := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < k
  · have hiJ : i < J := hi.trans_le hk
    have hip : i < pre.length := hp ▸ hi
    simp only [List.getElem?_take_of_lt hi, List.getElem?_ofFn, dif_pos hiJ, _root_.ThreeSum.StoredReporting.prefixRows,
      List.getElem?_eq_getElem hip, Option.getD_some]
  · rw [List.getElem?_take_eq_none (Nat.le_of_not_lt hi),
      List.getElem?_eq_none (by omega)]

theorem completions_eq_completedTuples {h J k : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (u : Fin J → Finset (Fin (464 * h))) :
    _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.completions q k ((List.ofFn u).take k) = _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.completedTuples q (_root_.ThreeSum.BlockRows.prefixIndices J k) u := by
  ext t
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.completions, _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.completedTuples, Finset.mem_filter, Finset.mem_univ, true_and,
    _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.partitionWord, _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.private_4ccb502193_ofFn_take_eq_iff, _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_prefixIndices]





section Indices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]























end Indices

end ThreeSum.StoredReporting

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact bridge from row-major machine masks to the block reporting query

The explicit coordinate equivalence sends the remaining blocks to a
contiguous suffix. Transport of finite subset sums identifies the machine's
Möbius value with the concrete forced-prefix count used by reporting.
-/

namespace ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.BlockIndexedQuery


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open scoped _root_.BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

@[simp] theorem prefixIndices_card {J k : ℕ} (hk : k ≤ J) :
    (_root_.ThreeSum.BlockRows.prefixIndices J k).card = k := by
  simpa only [_root_.ThreeSum.BlockRows.prefixIndices,Nat.min_eq_right hk] using (Fin.card_filter_val_lt (n := J) (m := k))























theorem querySet_card {J L h k : ℕ} (hk : k ≤ J) (Q : Fin J → Finset (Fin L))
    (hQ : ∀ i, (Q i).card = 2*h) : (_root_.ThreeSum.BlockIndexedQuery.querySet k Q).card = (J-k)*(2*h) := by
  rw [_root_.ThreeSum.BlockIndexedQuery.querySet,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.indexSet_card,_root_.ThreeSum.BlockForced.remaining,_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_card_of_balance _ _ (fun i _ => hQ i),
    Finset.card_compl,Fintype.card_fin,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.prefixIndices_card hk]







section Histograms

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]



















end Histograms

end ThreeSum.BlockIndexedQuery

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original-input histograms give the exact independently trimmed sources

The histogram keys retain the first modular reduction and the signed carry
offset. Looking up the endpoint's final residue therefore counts precisely
the original divisibility condition in `BlockEncoding`. An explicit finite
enumeration accounts for every original input incidence once.
-/

namespace ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.BlockSourceEncoding


open _root_.Finset
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightSourceResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
open scoped _root_.BigOperators

set_option maxHeartbeats 1000000

theorem key_eq_iff {p m : ℕ} (hm : 0 < m) (shift x endpoint : ℤ) :
    _root_.ThreeSum.LightSourceResidues.key p m shift x = _root_.ThreeSum.LightResidues.residue m 1 endpoint ↔
      (m : ℤ) ∣ x % (p : ℤ) + shift - endpoint := by
  rw [← Int.natCast_inj, _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.key_cast hm, _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_cast hm, one_mul,
    Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero]







theorem modulus_pos (h J : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J := pow_pos (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h) J

@[simp] theorem modulus_cast (h J : ℕ) : (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J : ℤ) = _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus,Nat.cast_pow]

section OriginalSources

variable {β : Type*} [DecidableEq β]





end OriginalSources

end ThreeSum.BlockSourceEncoding

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Finite terminal completions in the actual mask enumerator's order

At any valid reporting prefix, a full balanced endpoint needs exactly
`(J-k)*h` of the remaining query coordinates. Enumerating that one layer
contains every retained completion and costs no more than the terminal
Boolean-cube allowance. The selected bucket pair masses sum to at most the
unchanged original raw prefix count.
-/

namespace ThreeSum.ReportingHostTerminalChoices
open _root_.ThreeSum.ReportingHostTerminalChoices


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
open scoped _root_.BigOperators

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000



theorem choices_length {h J k : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (hk : k≤J) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices q k).length = ((J-k)*(2*h)).choose ((J-k)*h) := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices,List.length_map,_root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.missingSets_length]
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.querySet_card hk (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) (fun i => _root_.ThreeSum.LayerCounts.mem_vertices.mp (q i).2.property)]







theorem residual_card {h J k : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) (hk : k≤J) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.residual (_root_.ThreeSum.BlockRows.prefixIndices J k) t).card=(J-k)*h := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.residual,_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_card_of_balance _ _ (fun i _ => (_root_.ThreeSum.LocalGraph.edge_data (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge (t i))).1),
    Finset.card_compl,Fintype.card_fin,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.prefixIndices_card hk]

theorem completion_as_completed {h J k : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (pre : List (Finset (Fin (464*h)))) (hk : k≤J) (hp : _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix q k pre) :
    _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.completions q k pre=_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.completedTuples q (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum.StoredReporting.prefixRows pre) := by
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.completions_eq_completedTuples,_root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.take_prefixRows pre hp.1 hk]

theorem completion_residual_mem {h J k : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (pre : List (Finset (Fin (464*h)))) (hk : k≤J)
    (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) (ht : t∈_root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.completions q k pre) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.residual (_root_.ThreeSum.BlockRows.prefixIndices J k) t ∈ _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices q k := by
  apply (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.mem_choices q k _).mpr
  exact ⟨_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.residual_subset q _ t (Finset.mem_filter.mp ht).2.1,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.residual_card t hk⟩

theorem completion_endpoints {h J k : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (pre : List (Finset (Fin (464*h)))) (hk : k≤J) (hp : _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix q k pre)
    (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) (ht : t∈_root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.completions q k pre) :
    _root_.ThreeSum.BlockForced.prefixLeft (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum.StoredReporting.prefixRows pre) ∪ _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.residual (_root_.ThreeSum.BlockRows.prefixIndices J k) t=_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset t ∧
      _root_.ThreeSum.BlockForced.prefixRight (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) (_root_.ThreeSum.StoredReporting.prefixRows pre) ∪
        (_root_.ThreeSum.BlockForced.remaining (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) \ _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.residual (_root_.ThreeSum.BlockRows.prefixIndices J k) t)=_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightSubset t := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.completion_as_completed q pre hk hp] at ht
  exact ⟨_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.forced_left_completion q _ _ t ht,
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.forced_right_completion q _ _ (fun i hi => (hp.2 i (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_prefixIndices.mp hi)).1) t ht⟩

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]





end ThreeSum.ReportingHostTerminalChoices

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual terminal completion mask arrays

The existing exact coordinate enumerator is applied to the entire remaining
query set. It emits both full endpoint masks, so the independent endpoint
and bucket-test constructors can consume them without constructing tuples
or invoking an oracle. Every original retained completion occurs.
-/

namespace ThreeSum.LightReportingTerminalMasks
open _root_.ThreeSum.LightReportingTerminalMasks


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000











theorem choiceAt_eq_get {h J k i : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (hi : i<(_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices q k).length) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.choiceAt q k i=(_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices q k)[i] := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.choiceAt,List.getElem?_eq_getElem hi,Option.getD_some]

theorem completion_index {h J k : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (pre : List (Finset (Fin (464*h)))) (hk : k≤J) (hp : _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix q k pre)
    (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) (ht : t∈_root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.completions q k pre) :
    ∃ i<_root_.ThreeSum.LightReportingTerminalMasks.count h J k, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.leftAt q k pre i=_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset t ∧ _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.rightAt q k pre i=_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightSubset t := by
  obtain ⟨i,hi,hget⟩ := List.mem_iff_getElem.mp (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.completion_residual_mem q pre hk t ht)
  refine ⟨i,by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices_length q hk,_root_.ThreeSum.LightReportingTerminalMasks.count] using hi,?_⟩
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.leftAt,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.rightAt,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.choiceAt_eq_get q hi,hget]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.completion_endpoints q pre hk hp t ht





variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ}





end ThreeSum.LightReportingTerminalMasks

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch

open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.LightSourceResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
open _root_.ThreeSum.LightReportingTerminalMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
open scoped _root_.BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
section

theorem ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.hit_of_compatible__implementation_dca28e6600 {h J k NL NR : ℕ} (p : ℕ) (shift av : ℤ)
    (B : Finset β) (C : Finset γ) (b : β→ℤ) (c : γ→ℤ)
    (left right : ℕ→ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j))
    (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (pre : List (Finset (Fin (464*h)))) (hk : k≤J) (hp : _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix q k pre)
    (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) (ht : t∈_root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.completions q k pre) (bc : β×γ)
    (hbc : bc∈_root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.compatiblePairs (p : ℤ) shift B C b c t) (heq : c bc.2-b bc.1-av=0) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.Hit av p shift left right NL NR q k pre := by
  have hq := (Finset.mem_filter.mp ht).2.1
  obtain ⟨s,hs,hL,hR⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.completion_index q pre hk hp t ht
  obtain ⟨hmem,hdivL,hdivR⟩ := Finset.mem_filter.mp hbc
  obtain ⟨hb,hc⟩ := Finset.mem_product.mp hmem
  let i : Fin NL := eL.symm ⟨bc.1,hb⟩
  let j : Fin NR := eR.symm ⟨bc.2,hc⟩
  have hi : left i.val=b bc.1 := (hvL i).trans (by simp [i])
  have hj : right j.val=c bc.2 := (hvR j).trans (by simp [j])
  refine ⟨s,hs,?_,?_,i.val,i.isLt,j.val,j.isLt,?_,?_,?_⟩
  · change _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest.leftFlag (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.leftAt q k pre s)=1
    rw [hL]
    simp [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest.leftFlag,_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftAllowed_choice t q hq]
  · change _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest.rightFlag (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.rightAt q k pre s)=1
    rw [hR]
    simp [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest.rightFlag,_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightAllowed_choice t q hq]
  · apply (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.key_eq_iff (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus_pos h J) 0 (left i.val) _).mpr
    change (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J : ℤ) ∣ left i.val%(p : ℤ)+0-_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointLeft (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.leftAt q k pre s)
    simpa only [hi,hL,_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointLeft_choice t q hq,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus_cast,add_zero] using hdivL
  · apply (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.key_eq_iff (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus_pos h J) shift (right j.val) _).mpr
    change (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J : ℤ) ∣ right j.val%(p : ℤ)+shift-_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointRight (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.rightAt q k pre s)
    simpa only [hj,hR,_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointRight_choice t q hq,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus_cast] using hdivR
  · simpa only [hi,hj] using heq
end

end

theorem solution.{u_implementation_0,u_implementation_1} : type_of% (@ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.hit_of_compatible__implementation_dca28e6600.{u_implementation_0,u_implementation_1}) := (@ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.hit_of_compatible__implementation_dca28e6600.{u_implementation_0,u_implementation_1})

#print axioms solution
