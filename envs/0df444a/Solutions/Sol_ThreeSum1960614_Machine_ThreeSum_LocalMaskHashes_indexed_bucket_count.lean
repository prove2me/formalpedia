-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.indexed_bucket_count
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:08:44.436475+00:00
-- url     : https://prove2.me/submissions/25e7462d-c4a9-43a7-8028-6fc230e61678

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
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
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
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
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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
import Theorems.Thm_ThreeSum_SubsetAddress_enumerateLayer_nodup

namespace Finset
end Finset
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.LocalMaskGraph
end ThreeSum.LocalMaskGraph
namespace ThreeSum.LocalMaskHashes
end ThreeSum.LocalMaskHashes
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph
end ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph
namespace ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes
end ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes
namespace ThreeSum1960614.Machine.ThreeSum.MaskDecode
end ThreeSum1960614.Machine.ThreeSum.MaskDecode
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

namespace ThreeSum1960614.Machine

/-!
# Concrete integer indices for the local disjoint-subset graph

The finite list is the already checked layer-mask enumeration. Its Boolean
coordinate rows make disjointness an ordinary zero Boolean inner product.
-/

namespace ThreeSum.LocalMaskGraph
open _root_.ThreeSum.LocalMaskGraph


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.MaskDecode
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskDecode
open scoped _root_.BigOperators







theorem maskAt_spec {L h i : ℕ} (hi : i < _root_.ThreeSum.LocalMaskGraph.vertexCount L h) :
    _root_.ThreeSum.SubsetAddress.IsMask L h (_root_.ThreeSum.LocalMaskGraph.maskAt L h i) := (_root_.ThreeSum.SubsetAddress.mem_enumerateLayer L h _).mp (_root_.ThreeSum.LocalMaskGraph.maskAt_mem hi)



theorem subsetMask_setAt {L h i : ℕ} (hi : i < _root_.ThreeSum.LocalMaskGraph.vertexCount L h) :
    _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.LocalMaskGraph.setAt L h i) = _root_.ThreeSum.LocalMaskGraph.maskAt L h i := _root_.ThreeSum.MaskDecode.subsetMask_decode (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph.maskAt_spec hi).1

theorem maskAt_injective {L h i j : ℕ} (hi : i < _root_.ThreeSum.LocalMaskGraph.vertexCount L h) (hj : j < _root_.ThreeSum.LocalMaskGraph.vertexCount L h)
    (he : _root_.ThreeSum.LocalMaskGraph.maskAt L h i = _root_.ThreeSum.LocalMaskGraph.maskAt L h j) : i=j := by
  have hi' : i < (_root_.ThreeSum.SubsetAddress.enumerateLayer L h).length := by simpa [_root_.ThreeSum.LocalMaskGraph.vertexCount,_root_.ThreeSum.SubsetAddress.enumerateLayer_length] using hi
  have hj' : j < (_root_.ThreeSum.SubsetAddress.enumerateLayer L h).length := by simpa [_root_.ThreeSum.LocalMaskGraph.vertexCount,_root_.ThreeSum.SubsetAddress.enumerateLayer_length] using hj
  exact (List.getD_inj hi' hj' (_root_.ThreeSum.SubsetAddress.enumerateLayer_nodup L h)).mp he

theorem setAt_injective {L h i j : ℕ} (hi : i < _root_.ThreeSum.LocalMaskGraph.vertexCount L h) (hj : j < _root_.ThreeSum.LocalMaskGraph.vertexCount L h)
    (he : _root_.ThreeSum.LocalMaskGraph.setAt L h i = _root_.ThreeSum.LocalMaskGraph.setAt L h j) : i=j := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph.maskAt_injective hi hj
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph.subsetMask_setAt hi,← _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph.subsetMask_setAt hj,he]

theorem setAt_complete {L h : ℕ} (s : Finset (Fin L)) (hs : s.card=h) :
    ∃ i < _root_.ThreeSum.LocalMaskGraph.vertexCount L h, _root_.ThreeSum.LocalMaskGraph.setAt L h i=s := by
  have hm : _root_.ThreeSum.SubsetAddress.subsetMask s ∈ _root_.ThreeSum.SubsetAddress.enumerateLayer L h := (_root_.ThreeSum.SubsetAddress.mem_enumerateLayer L h _).mpr (by
    simpa only [hs] using _root_.ThreeSum.SubsetAddress.subsetMask_isMask s)
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hm
  refine ⟨i,by simpa [_root_.ThreeSum.LocalMaskGraph.vertexCount,_root_.ThreeSum.SubsetAddress.enumerateLayer_length] using hi,?_⟩
  unfold _root_.ThreeSum.LocalMaskGraph.setAt _root_.ThreeSum.LocalMaskGraph.maskAt
  rw [List.getD_eq_getElem _ _ hi,he,_root_.ThreeSum.MaskDecode.decode_subsetMask]









end ThreeSum.LocalMaskGraph

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes

open _root_.Finset
open _root_.ThreeSum.LocalMaskGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
variable {h L k : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.indexed_bucket_count__implementation_43a8616e69 (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h))
    (shape : Finset (Fin L) → (Fin L → Bool)) (hinj : Function.Injective shape)
    (code : ℕ → ℕ)
    (hcodeLt : ∀ i < _root_.ThreeSum.LocalMaskGraph.vertexCount L k, code i < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)
    (hcode : ∀ i < _root_.ThreeSum.LocalMaskGraph.vertexCount L k,
      (code i : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) = _root_.ThreeSum.HashFamily.hashValue w (shape (_root_.ThreeSum.LocalMaskGraph.setAt L k i)))
    {r : ℕ} (hr : r < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) :
    _root_.ThreeSum.LightHistogram.count code r (_root_.ThreeSum.LocalMaskGraph.vertexCount L k) =
      _root_.ThreeSum.HashFamily.bucketSize ((_root_.ThreeSum.LayerCounts.vertices L k).image shape) w (r : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) := by
  unfold _root_.ThreeSum.LightHistogram.count _root_.ThreeSum.HashFamily.bucketSize
  apply card_bij (fun i _ => shape (_root_.ThreeSum.LocalMaskGraph.setAt L k i))
  · intro i hi
    obtain ⟨hi,hci⟩ := mem_filter.mp hi
    have hi' := mem_range.mp hi
    refine mem_filter.mpr ⟨mem_image.mpr ⟨_root_.ThreeSum.LocalMaskGraph.setAt L k i,
      _root_.ThreeSum.LayerCounts.mem_vertices.mpr (_root_.ThreeSum.LocalMaskGraph.setAt_card hi'),rfl⟩,?_⟩
    rw [← hcode i hi',hci]
  · intro i hi j hj he
    exact _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph.setAt_injective (mem_range.mp (mem_filter.mp hi).1)
      (mem_range.mp (mem_filter.mp hj).1) (hinj he)
  · intro s hs
    obtain ⟨hs,hhash⟩ := mem_filter.mp hs
    obtain ⟨S,hS,rfl⟩ := mem_image.mp hs
    obtain ⟨i,hi,he⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph.setAt_complete S (_root_.ThreeSum.LayerCounts.mem_vertices.mp hS)
    have hcast : (code i : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) = (r : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) := by
      rw [hcode i hi,he]
      exact hhash
    have hci : code i = r := by
      have hv := congrArg ZMod.val hcast
      simpa only [ZMod.val_natCast_of_lt (hcodeLt i hi),ZMod.val_natCast_of_lt hr] using hv
    exact ⟨i,mem_filter.mpr ⟨mem_range.mpr hi,hci⟩,congrArg shape he⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.indexed_bucket_count__implementation_43a8616e69) := (@ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.indexed_bucket_count__implementation_43a8616e69)

#print axioms solution
