-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.localChildren_mem
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:16:30.207846+00:00
-- url     : https://prove2.me/submissions/41a2dba2-d3e6-4240-b6a3-8b2510a213cf

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
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
import Mathlib.Data.Finset.Card
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
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
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
import Theorems.Thm_ThreeSum_ReportingHostMasks_blockSet_localRow

namespace Finset
end Finset
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
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
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
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalGraph
end ThreeSum1960614.Machine.ThreeSum.LocalGraph
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
end ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
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









@[simp] theorem row_join {J L : ℕ} (I : Finset (Fin J))
    (u : Fin J → Finset (Fin L)) (i : Fin J) :
    _root_.ThreeSum.BlockRows.row (_root_.ThreeSum.BlockRows.join I u) i = if i ∈ I then u i else ∅ := by
  ext x
  by_cases hi : i ∈ I <;> simp [hi]

















theorem join_card {J L : ℕ} (I : Finset (Fin J)) (u : Fin J → Finset (Fin L)) :
    (_root_.ThreeSum.BlockRows.join I u).card = ∑ i ∈ I, (u i).card := Finset.card_sigma _ _













end ThreeSum.BlockRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Positive-prefix reporting for concrete guarded incidences

The band triple is fixed by the input index sets and offset passed to this
module. Its wanted queries retain the original A index, signed lift and
full output tuple, including every chosen-map occurrence. Children are
the balanced subsets of the next output block, in deterministic colex order.
-/

namespace ThreeSum.RawReporting
open _root_.ThreeSum.RawReporting


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





theorem mem_childList {L h : ℕ} {Q S : Finset (Fin L)} :
    S ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.childList Q h ↔ S ∈ Q.powersetCard h := by
  constructor
  · intro hs
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
    obtain ⟨s, hsLayer, rfl⟩ := Finset.mem_map.mp ((Finset.mem_sort _).mp hc)
    exact hsLayer
  · intro hs
    apply List.mem_map.mpr
    refine ⟨toColex S, ?_, rfl⟩
    apply (Finset.mem_sort _).mpr
    exact Finset.mem_map.mpr ⟨S, hs, rfl⟩


























section FixedBand

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]





















end FixedBand

end ThreeSum.RawReporting

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

@[simp] theorem unindex_index {J L : ℕ} (S : Finset (_root_.ThreeSum.BlockRows.Coord J L)) :
    _root_.ThreeSum.BlockIndex.unindexSet (_root_.ThreeSum.BlockIndex.indexSet S) = S := by
  ext c
  simp [_root_.ThreeSum.BlockIndex.unindexSet,_root_.ThreeSum.BlockIndex.indexSet]





@[simp] theorem indexSet_subset {J L : ℕ} (S T : Finset (_root_.ThreeSum.BlockRows.Coord J L)) :
    _root_.ThreeSum.BlockIndex.indexSet S ⊆ _root_.ThreeSum.BlockIndex.indexSet T ↔ S ⊆ T := by
  simp [_root_.ThreeSum.BlockIndex.indexSet]















end ThreeSum.BlockIndex

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



@[simp] theorem blockSet_subset {J L : ℕ} (i : Fin J) (S T : Finset (Fin L)) :
    _root_.ThreeSum.ReportingHostMasks.blockSet i S ⊆ _root_.ThreeSum.ReportingHostMasks.blockSet i T ↔ S ⊆ T := by
  rw [_root_.ThreeSum.ReportingHostMasks.blockSet,_root_.ThreeSum.ReportingHostMasks.blockSet,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.indexSet_subset]
  constructor
  · intro h x hx
    exact (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join.mp (h (x := Sigma.mk i x) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join.mpr ⟨by simp,hx⟩))).2
  · intro h ⟨j,x⟩ hx
    exact _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join.mpr ⟨(_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join.mp hx).1,h (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join.mp hx).2⟩



@[simp] theorem localRow_blockSet {J L : ℕ} (i : Fin J) (S : Finset (Fin L)) :
    _root_.ThreeSum.ReportingHostMasks.localRow i (_root_.ThreeSum.ReportingHostMasks.blockSet i S) = S := by
  simp [_root_.ThreeSum.ReportingHostMasks.localRow,_root_.ThreeSum.ReportingHostMasks.blockSet]











theorem globalChildren_mem {J L : ℕ} (i : Fin J) (Q S : Finset (Fin L)) (h : ℕ) :
    _root_.ThreeSum.ReportingHostMasks.blockSet i S ∈ _root_.ThreeSum.ReportingHostMasks.globalChildren i Q h ↔ S ⊆ Q ∧ S.card = h := by
  simp [_root_.ThreeSum.ReportingHostMasks.globalChildren,_root_.ThreeSum.QueryCoordinates.missingSets_mem]































end ThreeSum.ReportingHostMasks

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.ReportingHostMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks

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
section

theorem ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.localChildren_mem__implementation_e023d3b2e2 {J L : ℕ} (i : Fin J) (Q S : Finset (Fin L)) (h : ℕ) :
    S ∈ _root_.ThreeSum.ReportingHostMasks.localChildren i Q h ↔ S ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.childList Q h := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.mem_childList,Finset.mem_powersetCard]
  constructor
  · intro hs
    obtain ⟨T,hT,rfl⟩ := List.mem_map.mp hs
    have ht := (_root_.ThreeSum.QueryCoordinates.missingSets_mem _ _ _).mp hT
    have he := _root_.ThreeSum.ReportingHostMasks.blockSet_localRow i Q ht.1
    have hc : (_root_.ThreeSum.ReportingHostMasks.localRow i T).card = T.card := by
      simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.blockSet_card] using congrArg Finset.card he
    exact ⟨(_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.blockSet_subset i _ _).mp (he.symm ▸ ht.1),hc.trans ht.2⟩
  · intro hs
    exact List.mem_map.mpr ⟨_root_.ThreeSum.ReportingHostMasks.blockSet i S,(_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.globalChildren_mem i Q S h).mpr hs,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.localRow_blockSet i S⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.localChildren_mem__implementation_e023d3b2e2) := (@ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.localChildren_mem__implementation_e023d3b2e2)

#print axioms solution
