-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:46:25.062996+00:00
-- url     : https://prove2.me/submissions/857fe3c9-1b64-450d-9c96-ccc72ca3c20e

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingGatherPair_program_meets

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockMaskLayout
end ThreeSum.BlockMaskLayout
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.LightBlockChildrenIndexed
end ThreeSum.LightBlockChildrenIndexed
namespace ThreeSum.LightReportingFilter
end ThreeSum.LightReportingFilter
namespace ThreeSum.LightReportingPositiveMasks
end ThreeSum.LightReportingPositiveMasks
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
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
namespace ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
end ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
end ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingFilter
end ThreeSum1960614.Machine.ThreeSum.LightReportingFilter
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks
end ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
end ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
end ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

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





































theorem join_card {J L : ℕ} (I : Finset (Fin J)) (u : Fin J → Finset (Fin L)) :
    (_root_.ThreeSum.BlockRows.join I u).card = ∑ i ∈ I, (u i).card := Finset.card_sigma _ _













end ThreeSum.BlockRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Segments of the memory

Seg μ a l says that the cells a, a + 1, …, a + l.length - 1 of the memory μ hold the list l.
SegN is Seg for a list of natural numbers, MatAt for a matrix written row by row, VecAt for a vector
of indices.  The file has the lemmas for reading a cell of a segment, writing into it, writing
elsewhere, and for cutting and joining segments.  Each of the four predicates has its lemma `keep`,
which carries it to a later memory.
-/

@[expose] public section

namespace Light
open _root_.Light


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp





variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}





















































/-- Reading a cell of a segment of natural numbers, with the proof that the index is in range. -/
theorem SegN.getElem {l : List ℕ} (h : _root_.ThreeSum1960614.Machine.Light.SegN μ a l) {i : ℕ} (hi : i < l.length) :
    μ (a + i) = (l[i] : ℕ) := by
  rw [h i (by simpa using hi), List.getElem_map]

























end Light

end

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
# Actual positive-query filtering for a reporting frontier

The scan writes exactly the indices of positive stored query counts, in input
order. Its cost is linear in the candidate count, and original input arrays
are preserved. It does not recompute or assume the query implementation.
-/

namespace ThreeSum.LightReportingFilter
open _root_.ThreeSum.LightReportingFilter


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}











@[simp] theorem mem_selected (count : ℕ → ℕ) (j i : ℕ) :
    i ∈ _root_.ThreeSum.LightReportingFilter.selected count j ↔ i < j ∧ 0 < count i := by
  simp [_root_.ThreeSum.LightReportingFilter.selected]

















end ThreeSum.LightReportingFilter

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
# Exact next-block masks for the reporting host

The machine enumerates subsets directly in the global row-major ground set.
This file identifies those subsets with the balanced next-row children of
the original reporting tree, and proves the arithmetic mask transitions.
-/

namespace ThreeSum.ReportingHostMasks
open _root_.ThreeSum.ReportingHostMasks


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.BlockMaskLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced





@[simp] theorem blockSet_card {J L : ℕ} (i : Fin J) (S : Finset (Fin L)) :
    (_root_.ThreeSum.ReportingHostMasks.blockSet i S).card = S.card := by
  simp [_root_.ThreeSum.ReportingHostMasks.blockSet,_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_card]















@[simp] theorem globalChildren_length {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :
    (_root_.ThreeSum.ReportingHostMasks.globalChildren i Q h).length = Q.card.choose h := by
  simp [_root_.ThreeSum.ReportingHostMasks.globalChildren]









@[simp] theorem localChildren_length {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :
    (_root_.ThreeSum.ReportingHostMasks.localChildren i Q h).length = Q.card.choose h := by
  simp [_root_.ThreeSum.ReportingHostMasks.localChildren]

























end ThreeSum.ReportingHostMasks

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # The concrete child constructor extends the original valid reporting prefixes -/

namespace ThreeSum.LightBlockChildrenIndexed
open _root_.ThreeSum.LightBlockChildrenIndexed


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockMaskLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum.ReportingHostMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}



theorem childPrefixes_length {h J k : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (pre : List (Finset (Fin (464*h)))) (hk : k < J) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childPrefixes q pre hk).length = _root_.ThreeSum.LocalCoverBounds.groupSize h := by
  have hc : (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q ⟨k,hk⟩).card = 2*h :=
    _root_.ThreeSum.LayerCounts.mem_vertices.mp (q ⟨k,hk⟩).2.property
  simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childPrefixes,hc,_root_.ThreeSum.LocalCoverBounds.groupSize]













theorem childAt_eq_get {h J k : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (pre : List (Finset (Fin (464*h)))) (hk : k < J) (i : ℕ) (hi : i < _root_.ThreeSum.LocalCoverBounds.groupSize h) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childAt q pre hk i = (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childPrefixes q pre hk)[i]'(by rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childPrefixes_length]; exact hi) := by
  have hib : i < (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childPrefixes q pre hk).length := by rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childPrefixes_length]; exact hi
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childAt,List.getElem?_eq_getElem hib,Option.getD_some]







end ThreeSum.LightBlockChildrenIndexed

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual gathered positive mask arrays are the exact original next-prefix list -/

namespace ThreeSum.LightReportingPositiveMasks
open _root_.ThreeSum.LightReportingPositiveMasks


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive

set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false

theorem ofFn_getD_map {α β : Type*} (xs : List α) (fallback : α) (f : α → β) :
    List.ofFn (fun i : Fin xs.length => f (xs[i.val]?.getD fallback)) = xs.map f := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  have hi'' : i < xs.length := by simpa only [List.length_map] using hi'
  simp only [List.getElem_ofFn,List.getElem_map,List.getElem?_eq_getElem hi'',Option.getD_some]

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]



theorem selected_index_lt {h J k : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (pre : List (Finset (Fin (464*h)))) (hk : k < J)
    {i : ℕ} (hi : i < (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk)[i]?.getD 0 < _root_.ThreeSum.LocalCoverBounds.groupSize h := by
  rw [List.getElem?_eq_getElem hi,Option.getD_some]
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFilter.mem_selected _ _ _).mp (List.getElem_mem hi) |>.1



end ThreeSum.LightReportingPositiveMasks

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.program_meets__implementation_66726212f7 {μ : ℕ → ℤ} {h J k indices srcL srcR dstL dstR d : ℕ}
    (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ)) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)
    (pre : List (Finset (Fin (464*h)))) (hk : k < J)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hindices : indices+(_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length ≤ lim.space)
    (hsrcL : srcL+_root_.ThreeSum.LocalCoverBounds.groupSize h ≤ lim.space) (hsrcR : srcR+_root_.ThreeSum.LocalCoverBounds.groupSize h ≤ lim.space)
    (hdstL : dstL+(_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length ≤ lim.space)
    (hdstR : dstR+(_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length ≤ lim.space)
    (hsepIL : _root_.Light.Apart indices (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length dstL (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length)
    (hsepIR : _root_.Light.Apart indices (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length dstR (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length)
    (hsepLL : _root_.Light.Apart srcL (_root_.ThreeSum.LocalCoverBounds.groupSize h) dstL (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length)
    (hsepRL : _root_.Light.Apart srcR (_root_.ThreeSum.LocalCoverBounds.groupSize h) dstL (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length)
    (hsepRR : _root_.Light.Apart srcR (_root_.ThreeSum.LocalCoverBounds.groupSize h) dstR (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length)
    (hsepOut : _root_.Light.Apart dstL (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length dstR (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length)
    (hreadI : _root_.ThreeSum1960614.Machine.Light.SegN μ indices (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk))
    (hreadL : _root_.ThreeSum1960614.Machine.Light.SegN μ srcL ((_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childPrefixes w.2.2 pre hk).map fun next =>
      _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.leftPrefix (k+1) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) next))))
    (hreadR : _root_.ThreeSum1960614.Machine.Light.SegN μ srcR ((_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childPrefixes w.2.2 pre hk).map fun next =>
      _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.rightPrefix (k+1) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) next))))
    (hword : ((2^(J*(464*h)+1) : ℕ) : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingGatherPair.program 1 d
      [indices,srcL,srcR,(_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length,_root_.ThreeSum.LocalCoverBounds.groupSize h,dstL,dstR]
      μ (_root_.ThreeSum.LightReportingGatherPair.time (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length)
      (fun _ ν =>
        _root_.ThreeSum1960614.Machine.Light.SegN ν dstL ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.positiveChildren I w pre hk).map fun next =>
          _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.leftPrefix (k+1) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) next))) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN ν dstR ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.positiveChildren I w pre hk).map fun next =>
          _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.rightPrefix (k+1) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) next))) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside2 μ ν dstL (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length dstR (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length) := by
  let index : ℕ → ℕ := fun i => (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk)[i]?.getD 0
  let left : ℕ → ℤ := fun i => (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.leftPrefix (k+1) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childAt w.2.2 pre hk i))) : ℤ)
  let right : ℕ → ℤ := fun i => (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.rightPrefix (k+1) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2)
    (_root_.ThreeSum.StoredReporting.prefixRows (J := J) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childAt w.2.2 pre hk i))) : ℤ)
  have hI (i : ℕ) (hi : i < (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length) : μ (indices+i) = (index i : ℤ) := by
    have hh := hreadI.getElem hi
    simpa only [index,List.getElem?_eq_getElem hi,Option.getD_some] using hh
  have hL (i : ℕ) (hi : i < _root_.ThreeSum.LocalCoverBounds.groupSize h) : μ (srcL+i) = left i := by
    unfold left
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childAt_eq_get w.2.2 pre hk i hi]
    have hh := hreadL.getElem (i := i) (by simpa only [List.length_map,_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childPrefixes_length] using hi)
    simpa only [List.getElem_map] using hh
  have hR (i : ℕ) (hi : i < _root_.ThreeSum.LocalCoverBounds.groupSize h) : μ (srcR+i) = right i := by
    unfold right
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childAt_eq_get w.2.2 pre hk i hi]
    have hh := hreadR.getElem (i := i) (by simpa only [List.length_map,_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childPrefixes_length] using hi)
    simpa only [List.getElem_map] using hh
  have hmask (U : Finset (Fin (J*(464*h)))) : |(_root_.ThreeSum.SubsetAddress.subsetMask U : ℤ)| ≤ lim.word := by
    rw [Int.abs_natCast]
    exact (Int.ofNat_le.mpr ((_root_.ThreeSum.SubsetAddress.subsetMask_isMask U).1.le.trans
      (Nat.pow_le_pow_right (by decide) (by omega)))).trans hword
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingGatherPair.program_meets (d := d) (μ := μ) index left right
    hw hindices hsrcL hsrcR hdstL hdstR hsepIL hsepIR hsepLL hsepRL hsepRR hsepOut
    (fun i hi => _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selected_index_lt I w pre hk hi) hI hL hR
    (fun _ _ => hmask _) (fun _ _ => hmask _) hd
  have heL : List.ofFn (fun i : Fin (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length => left (index i.val)) =
      (((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.positiveChildren I w pre hk).map fun next => _root_.ThreeSum.SubsetAddress.subsetMask
        (_root_.ThreeSum.BlockIndexedQuery.leftPrefix (k+1) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) next))).map fun x : ℕ => (x : ℤ)) := by
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.ofFn_getD_map (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk) 0 left]
    simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.positiveChildren,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices,List.map_map,left,Function.comp_def]
  have heR : List.ofFn (fun i : Fin (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length => right (index i.val)) =
      (((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.positiveChildren I w pre hk).map fun next => _root_.ThreeSum.SubsetAddress.subsetMask
        (_root_.ThreeSum.BlockIndexedQuery.rightPrefix (k+1) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) next))).map fun x : ℕ => (x : ℤ)) := by
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.ofFn_getD_map (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk) 0 right]
    simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.positiveChildren,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices,List.map_map,right,Function.comp_def]
  rw [heL,heR] at hh
  exact hh
end

end

theorem solution.{u_implementation_0,u_implementation_1,u_implementation_2} : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.program_meets__implementation_66726212f7.{u_implementation_0,u_implementation_1,u_implementation_2}) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.program_meets__implementation_66726212f7.{u_implementation_0,u_implementation_1,u_implementation_2})

#print axioms solution
