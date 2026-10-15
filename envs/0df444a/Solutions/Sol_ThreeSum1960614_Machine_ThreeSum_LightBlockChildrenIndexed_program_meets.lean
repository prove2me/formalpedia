-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:09:26.810335+00:00
-- url     : https://prove2.me/submissions/e7b80e9e-1bf4-4e20-8cbf-12eaa0bf0ebf

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBlockChildren_meets
import Theorems.Thm_ThreeSum_ReportingHostMasks_blockSet_localRow
import Theorems.Thm_ThreeSum_ReportingHostMasks_prefixRows_append
import Theorems.Thm_ThreeSum_ReportingHostMasks_querySet_step

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
namespace ThreeSum.LightBlockChildren
end ThreeSum.LightBlockChildren
namespace ThreeSum.LightBlockChildrenIndexed
end ThreeSum.LightBlockChildrenIndexed
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.MaskDifference
end ThreeSum.MaskDifference
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
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
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockChildren
end ThreeSum1960614.Machine.ThreeSum.LightBlockChildren
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
end ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.MaskDifference
end ThreeSum1960614.Machine.ThreeSum.MaskDifference
namespace ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
end ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
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



























theorem join_card {J L : ℕ} (I : Finset (Fin J)) (u : Fin J → Finset (Fin L)) :
    (_root_.ThreeSum.BlockRows.join I u).card = ∑ i ∈ I, (u i).card := Finset.card_sigma _ _









@[simp] theorem mem_prefixIndices {J k : ℕ} {i : Fin J} :
    i ∈ _root_.ThreeSum.BlockRows.prefixIndices J k ↔ i.val < k := by simp [_root_.ThreeSum.BlockRows.prefixIndices]



end ThreeSum.BlockRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact arithmetic subtraction of one subset mask from another -/

namespace ThreeSum.MaskDifference
open _root_.ThreeSum.MaskDifference


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress

theorem subsetMask_sum {L : ℕ} (S : Finset (Fin L)) :
    _root_.ThreeSum.SubsetAddress.subsetMask S = ∑ i ∈ S, 2^i.val := by
  simp [_root_.ThreeSum.SubsetAddress.subsetMask,_root_.ThreeSum.SubsetAddress.maskOf,_root_.ThreeSum.SubsetAddress.natPositions]











end ThreeSum.MaskDifference

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



@[simp] theorem coordEquiv_val {J L : ℕ} (i : Fin J) (x : Fin L) :
    (_root_.ThreeSum.BlockIndex.coordEquiv J L ⟨i,x⟩).val = i.val*L+x.val := by
  simp [_root_.ThreeSum.BlockIndex.coordEquiv, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]





@[simp] theorem mem_indexSet {J L : ℕ} (S : Finset (_root_.ThreeSum.BlockRows.Coord J L)) (c : _root_.ThreeSum.BlockRows.Coord J L) :
    _root_.ThreeSum.BlockIndex.coordEquiv J L c ∈ _root_.ThreeSum.BlockIndex.indexSet S ↔ c ∈ S := by
  simp [_root_.ThreeSum.BlockIndex.indexSet]

@[simp] theorem indexSet_card {J L : ℕ} (S : Finset (_root_.ThreeSum.BlockRows.Coord J L)) :
    (_root_.ThreeSum.BlockIndex.indexSet S).card = S.card := Finset.card_map _























end ThreeSum.BlockIndex

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact row-major mask packing and prefix scan invariants -/

namespace ThreeSum.BlockMaskLayout
open _root_.ThreeSum.BlockMaskLayout


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open scoped _root_.BigOperators





theorem mask_join {J L : ℕ} (I : Finset (Fin J)) (rows : Fin J → Finset (Fin L)) :
    _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndex.indexSet (_root_.ThreeSum.BlockRows.join I rows)) = ∑ i ∈ I, _root_.ThreeSum.BlockMaskLayout.rowMask rows i := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.MaskDifference.subsetMask_sum]
  unfold _root_.ThreeSum.BlockIndex.indexSet
  rw [Finset.sum_map]
  unfold _root_.ThreeSum.BlockRows.join
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Equiv.toEmbedding_apply,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.coordEquiv_val,pow_add,_root_.ThreeSum.BlockMaskLayout.rowMask,
    _root_.ThreeSum1960614.Machine.ThreeSum.MaskDifference.subsetMask_sum,Finset.mul_sum]

























end ThreeSum.BlockMaskLayout

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



@[simp] theorem mem_blockSet {J L : ℕ} (i j : Fin J) (S : Finset (Fin L)) (x : Fin L) :
    _root_.ThreeSum.BlockIndex.coordEquiv J L ⟨j,x⟩ ∈ _root_.ThreeSum.ReportingHostMasks.blockSet i S ↔ j = i ∧ x ∈ S := by
  simp [_root_.ThreeSum.ReportingHostMasks.blockSet]

@[simp] theorem blockSet_card {J L : ℕ} (i : Fin J) (S : Finset (Fin L)) :
    (_root_.ThreeSum.ReportingHostMasks.blockSet i S).card = S.card := by
  simp [_root_.ThreeSum.ReportingHostMasks.blockSet,_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_card]

@[simp] theorem blockSet_mask {J L : ℕ} (i : Fin J) (S : Finset (Fin L)) :
    _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.ReportingHostMasks.blockSet i S) = 2^(i.val*L)*_root_.ThreeSum.SubsetAddress.subsetMask S := by
  simp [_root_.ThreeSum.ReportingHostMasks.blockSet,_root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout.mask_join,_root_.ThreeSum.BlockMaskLayout.rowMask]



























theorem leftPrefix_step {J L k : ℕ} (u : Fin J → Finset (Fin L)) (hk : k < J)
    (S : Finset (Fin L)) :
    _root_.ThreeSum.BlockIndexedQuery.leftPrefix (k+1) (Function.update u ⟨k,hk⟩ S) =
      _root_.ThreeSum.BlockIndexedQuery.leftPrefix k u ∪ _root_.ThreeSum.ReportingHostMasks.blockSet ⟨k,hk⟩ S := by
  ext x
  obtain ⟨⟨i,a⟩,rfl⟩ := (_root_.ThreeSum.BlockIndex.coordEquiv J L).surjective x
  simp only [_root_.ThreeSum.BlockIndexedQuery.leftPrefix,_root_.ThreeSum.BlockForced.prefixLeft,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.mem_indexSet,_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join,_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_prefixIndices,
    Finset.mem_union,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.mem_blockSet]
  by_cases he : i = ⟨k,hk⟩
  · subst i
    simp
  · have hv : i.val ≠ k := fun h => he (Fin.ext h)
    have hi : i.val < k+1 ↔ i.val < k := by omega
    simp [he,hi]

theorem prefix_disjoint_block {J L k : ℕ} (u : Fin J → Finset (Fin L)) (hk : k < J)
    (S : Finset (Fin L)) : Disjoint (_root_.ThreeSum.BlockIndexedQuery.leftPrefix k u) (_root_.ThreeSum.ReportingHostMasks.blockSet ⟨k,hk⟩ S) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨⟨i,a⟩,rfl⟩ := (_root_.ThreeSum.BlockIndex.coordEquiv J L).surjective x
  obtain ⟨rfl,_⟩ := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.mem_blockSet _ _ _ _).mp hy
  have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join.mp (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.mem_indexSet _ _ |>.mp hx)).1
  exact (by simp : (⟨k,hk⟩ : Fin J) ∉ prefixIndices J k) hh

theorem rightPrefix_step {J L k : ℕ} (Q u : Fin J → Finset (Fin L)) (hk : k < J)
    (S : Finset (Fin L)) :
    _root_.ThreeSum.BlockIndexedQuery.rightPrefix (k+1) Q (Function.update u ⟨k,hk⟩ S) =
      _root_.ThreeSum.BlockIndexedQuery.rightPrefix k Q u ∪ _root_.ThreeSum.ReportingHostMasks.blockSet ⟨k,hk⟩ (Q ⟨k,hk⟩ \ S) := by
  have he : (fun i => Q i \ Function.update u ⟨k,hk⟩ S i) =
      Function.update (fun i => Q i \ u i) ⟨k,hk⟩ (Q ⟨k,hk⟩ \ S) := by
    funext i
    by_cases hi : i = ⟨k,hk⟩
    · subst i; simp
    · simp [hi]
  change _root_.ThreeSum.BlockIndexedQuery.leftPrefix (k+1) (fun i => Q i \ Function.update u ⟨k,hk⟩ S i) = _
  rw [he,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.leftPrefix_step]
  rfl







theorem blockSet_subset_query {J L k : ℕ} (Q : Fin J → Finset (Fin L)) (hk : k < J) :
    _root_.ThreeSum.ReportingHostMasks.blockSet ⟨k,hk⟩ (Q ⟨k,hk⟩) ⊆ _root_.ThreeSum.BlockIndexedQuery.querySet k Q := by
  intro x hx
  obtain ⟨⟨i,a⟩,rfl⟩ := (_root_.ThreeSum.BlockIndex.coordEquiv J L).surjective x
  obtain ⟨rfl,ha⟩ := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.mem_blockSet _ _ _ _).mp hx
  simp only [_root_.ThreeSum.BlockIndexedQuery.querySet,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.mem_indexSet,_root_.ThreeSum.BlockForced.remaining,_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join,Finset.mem_compl,_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_prefixIndices]
  exact ⟨by simp,ha⟩









end ThreeSum.ReportingHostMasks

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual construction of every next-block reporting child

The fixed program enumerates the balanced subsets of the next block directly
in global coordinates. Two affine scans then write the exact left and right
prefix masks of every child, and subtraction returns the next residual mask.
All enumeration and scan execution is discharged by concrete procedures.
-/

namespace ThreeSum.LightBlockChildren
open _root_.ThreeSum.LightBlockChildren


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
open _root_.ThreeSum.ReportingHostMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

















theorem program_meets {μ : ℕ → ℤ} {W h masks dstL dstR work d : ℕ}
    (A B Q R : Finset (Fin W))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hAQ : Disjoint A Q) (hBQ : Disjoint B Q) (hQR : Q ⊆ R)
    (hh : h ≤ Q.card+1)
    (hmasks : masks+Q.card.choose h ≤ dstL)
    (hleft : dstL+Q.card.choose h ≤ dstR)
    (hright : dstR+Q.card.choose h ≤ work)
    (hspace : work+(2*W+2) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+W+3 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildren.program 0 d
      [W,h,_root_.ThreeSum.SubsetAddress.subsetMask Q,_root_.ThreeSum.SubsetAddress.subsetMask A,_root_.ThreeSum.SubsetAddress.subsetMask B,_root_.ThreeSum.SubsetAddress.subsetMask R,masks,dstL,dstR,work]
      μ (_root_.ThreeSum.LightBlockChildren.time W Q.card h)
      (fun r μ' =>
        r = (_root_.ThreeSum.SubsetAddress.subsetMask (R \ Q) : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' masks ((_root_.ThreeSum.QueryCoordinates.missingSets Q h).map _root_.ThreeSum.SubsetAddress.subsetMask) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' dstL (_root_.ThreeSum.LightBlockChildren.leftMasks A Q h) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' dstR (_root_.ThreeSum.LightBlockChildren.rightMasks B Q h) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ μ' masks) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildren.meets rfl _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildren.procs A B Q R hw hAQ hBQ hQR hh hmasks hleft hright hspace hword hd



end ThreeSum.LightBlockChildren

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







section

private theorem private_8250857b77_leftMasks_eq {h J k : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (pre : List (Finset (Fin (464*h)))) (hp : pre.length = k) (hk : k < J) :
    _root_.ThreeSum.LightBlockChildren.leftMasks (_root_.ThreeSum.BlockIndexedQuery.leftPrefix k (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre))
        (_root_.ThreeSum.ReportingHostMasks.blockSet ⟨k,hk⟩ (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q ⟨k,hk⟩)) h =
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childPrefixes q pre hk).map fun next => _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.leftPrefix (k+1) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) next)) := by
  simp only [_root_.ThreeSum.LightBlockChildren.leftMasks,_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childPrefixes,_root_.ThreeSum.ReportingHostMasks.localChildren,_root_.ThreeSum.ReportingHostMasks.globalChildren,List.map_map]
  apply List.map_congr_left
  intro T hT
  have ht := (_root_.ThreeSum.QueryCoordinates.missingSets_mem _ _ _).mp hT
  simp only [Function.comp_apply]
  rw [_root_.ThreeSum.ReportingHostMasks.prefixRows_append pre hp hk,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.leftPrefix_step,
    _root_.ThreeSum.ReportingHostMasks.blockSet_localRow _ _ ht.1]
end


section

private theorem private_ebcc9a954a_rightMasks_eq {h J k : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (pre : List (Finset (Fin (464*h)))) (hp : pre.length = k) (hk : k < J) :
    _root_.ThreeSum.LightBlockChildren.rightMasks (_root_.ThreeSum.BlockIndexedQuery.rightPrefix k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre))
        (_root_.ThreeSum.ReportingHostMasks.blockSet ⟨k,hk⟩ (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q ⟨k,hk⟩)) h =
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childPrefixes q pre hk).map fun next =>
        _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.rightPrefix (k+1) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) next)) := by
  simp only [_root_.ThreeSum.LightBlockChildren.rightMasks,_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childPrefixes,_root_.ThreeSum.ReportingHostMasks.localChildren,_root_.ThreeSum.ReportingHostMasks.globalChildren,List.map_map]
  apply List.map_congr_left
  intro T hT
  have ht := (_root_.ThreeSum.QueryCoordinates.missingSets_mem _ _ _).mp hT
  have he : _root_.ThreeSum.ReportingHostMasks.blockSet ⟨k,hk⟩ (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q ⟨k,hk⟩ \ _root_.ThreeSum.ReportingHostMasks.localRow ⟨k,hk⟩ T) =
      _root_.ThreeSum.ReportingHostMasks.blockSet ⟨k,hk⟩ (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q ⟨k,hk⟩) \ T := by
    have heT := _root_.ThreeSum.ReportingHostMasks.blockSet_localRow ⟨k,hk⟩ (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q ⟨k,hk⟩) ht.1
    conv_rhs => rw [← heT]
    ext x
    obtain ⟨⟨i,a⟩,rfl⟩ := (_root_.ThreeSum.BlockIndex.coordEquiv J (464*h)).surjective x
    simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.mem_blockSet,Finset.mem_sdiff]
    tauto
  simp only [Function.comp_apply]
  rw [_root_.ThreeSum.ReportingHostMasks.prefixRows_append pre hp hk,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.rightPrefix_step,he]
end
















end ThreeSum.LightBlockChildrenIndexed

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed

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
section

theorem ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.program_meets__implementation_c063782c34 {μ : ℕ → ℤ} {h J k masks dstL dstR work d : ℕ}
    (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (pre : List (Finset (Fin (464*h))))
    (hp : _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix q k pre) (hk : k < J)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hmasks : masks+_root_.ThreeSum.LocalCoverBounds.groupSize h ≤ dstL)
    (hleft : dstL+_root_.ThreeSum.LocalCoverBounds.groupSize h ≤ dstR)
    (hright : dstR+_root_.ThreeSum.LocalCoverBounds.groupSize h ≤ work)
    (hspace : work+(2*(J*(464*h))+2) ≤ lim.space)
    (hword : ((2^(J*(464*h)+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+J*(464*h)+3 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildren.program 0 d
      [J*(464*h),h,_root_.ThreeSum.BlockMaskLayout.rowMask (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) ⟨k,hk⟩,
        _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.leftPrefix k (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre)),
        _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.rightPrefix k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre)),
        _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.querySet k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q)),masks,dstL,dstR,work]
      μ (_root_.ThreeSum.LightBlockChildren.time (J*(464*h)) (2*h) h)
      (fun r μ' =>
        r = (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.querySet (k+1) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q)) : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' masks ((_root_.ThreeSum.ReportingHostMasks.globalChildren ⟨k,hk⟩ (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q ⟨k,hk⟩) h).map _root_.ThreeSum.SubsetAddress.subsetMask) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' dstL ((_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childPrefixes q pre hk).map fun next =>
          _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.leftPrefix (k+1) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) next))) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' dstR ((_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childPrefixes q pre hk).map fun next =>
          _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.rightPrefix (k+1) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) next))) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ μ' masks) := by
  have hc : (_root_.ThreeSum.ReportingHostMasks.blockSet ⟨k,hk⟩ (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q ⟨k,hk⟩)).card = 2*h := by
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.blockSet_card]
    exact _root_.ThreeSum.LayerCounts.mem_vertices.mp (q ⟨k,hk⟩).2.property
  have hcount : (_root_.ThreeSum.ReportingHostMasks.blockSet ⟨k,hk⟩ (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q ⟨k,hk⟩)).card.choose h = _root_.ThreeSum.LocalCoverBounds.groupSize h := by
    rw [hc]
    rfl
  have hcall := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildren.program_meets (μ := μ) (d := d)
    (_root_.ThreeSum.BlockIndexedQuery.leftPrefix k (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre))
    (_root_.ThreeSum.BlockIndexedQuery.rightPrefix k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre))
    (_root_.ThreeSum.ReportingHostMasks.blockSet ⟨k,hk⟩ (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q ⟨k,hk⟩)) (_root_.ThreeSum.BlockIndexedQuery.querySet k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q))
    hw (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.prefix_disjoint_block _ hk _) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.prefix_disjoint_block _ hk _)
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.blockSet_subset_query _ hk) (by rw [hc]; omega)
    (hcount ▸ hmasks) (hcount ▸ hleft) (hcount ▸ hright) hspace hword hd
  have hrow : _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.ReportingHostMasks.blockSet ⟨k,hk⟩ (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q ⟨k,hk⟩)) = _root_.ThreeSum.BlockMaskLayout.rowMask (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) ⟨k,hk⟩ := by
    simp [_root_.ThreeSum.BlockMaskLayout.rowMask]
  rw [hrow,hc,_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.private_8250857b77_leftMasks_eq q pre hp.1 hk,_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.private_ebcc9a954a_rightMasks_eq q pre hp.1 hk,
    ← _root_.ThreeSum.ReportingHostMasks.querySet_step (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) hk] at hcall
  exact hcall
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.program_meets__implementation_c063782c34) := (@ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.program_meets__implementation_c063782c34)

#print axioms solution
