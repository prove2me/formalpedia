-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.WantedRecordCoverage.output_complete
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T08:58:52.721161+00:00
-- url     : https://prove2.me/submissions/408047c4-3e97-4277-aaca-3bba71058c6b

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
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
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
import Lean
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
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
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
import Mathlib.Data.List.Range
import Mathlib.Data.List.TakeDrop
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
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
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

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.LocalMaskGraph
end ThreeSum.LocalMaskGraph
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSum.RawAKeyLists
end ThreeSum.RawAKeyLists
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.WantedRecordCoverage
end ThreeSum.WantedRecordCoverage
namespace ThreeSum.WantedRecordOrder
end ThreeSum.WantedRecordOrder
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
end ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalGraph
end ThreeSum1960614.Machine.ThreeSum.LocalGraph
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph
end ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph
namespace ThreeSum1960614.Machine.ThreeSum.MaskDecode
end ThreeSum1960614.Machine.ThreeSum.MaskDecode
namespace ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
end ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
namespace ThreeSum1960614.Machine.ThreeSum.RawAKeyLists
end ThreeSum1960614.Machine.ThreeSum.RawAKeyLists
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.WantedRecordCoverage
end ThreeSum1960614.Machine.ThreeSum.WantedRecordCoverage
namespace ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder
end ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder

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

namespace ThreeSum1960614.Machine

/-!
# Literal global-output records behind the radix key array

Local records use the verified layer enumerator's order and retain every
schedule occurrence. Cartesian extension enumerates each original global
output once. Mapping to integers may introduce equal values; the key array
retains all of those separate incidences.
-/

namespace ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.GlobalKeyEnumeration


open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.RadixKeyLists
open _root_.ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
open scoped _root_.BigOperators

set_option maxHeartbeats 1800000





theorem layerRecord_surjective (h : ℕ) : Function.Surjective (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.layerRecord h) := by
  intro Q
  obtain ⟨i,hi,he⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph.setAt_complete Q.val
    (_root_.ThreeSum.LayerCounts.mem_vertices.mp Q.property)
  exact ⟨⟨i,hi⟩,Subtype.ext he⟩





theorem mem_layers (h : ℕ) (Q : {Q // Q ∈ _root_.ThreeSum.LayerCounts.vertices (464*h) (2*h)}) :
    Q ∈ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.layers h := by
  obtain ⟨i,rfl⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.layerRecord_surjective h Q
  exact List.mem_ofFn.mpr ⟨i,rfl⟩







theorem mem_localRecords (h : ℕ) (b : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.OutputBlock h) : b ∈ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.localRecords h := by
  exact List.mem_product.mpr ⟨List.mem_finRange _,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.mem_layers h b.2⟩













theorem mem_globalRecords (h J : ℕ) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) :
    q ∈ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalRecords h J := by
  have hx : List.ofFn q ∈ _root_.ThreeSum.RadixKeyLists.tuples (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.localRecords h) J :=
    (_root_.ThreeSum.RadixKeyLists.mem_tuples _ _ _).mpr ⟨List.length_ofFn,fun b _ => _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.mem_localRecords h b⟩
  apply List.mem_map.mpr
  refine ⟨⟨List.ofFn q,hx⟩,by simp,?_⟩
  funext i
  simp [_root_.ThreeSum.GlobalKeyEnumeration.tupleOfList]















end ThreeSum.GlobalKeyEnumeration

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original A positions and all three guarded lifts

The physical key order is lift-major, preserving every original position.
The selected-offset count is transported to the unchanged guarded wanted
labels used by raw reporting, including repeated input values.
-/

namespace ThreeSum.RawAKeyLists
open _root_.ThreeSum.RawAKeyLists


open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open scoped _root_.BigOperators

set_option maxHeartbeats 900000













theorem mem_records (xs : List ℤ) (r : _root_.ThreeSum.RawAKeyLists.Record xs) : r ∈ _root_.ThreeSum.RawAKeyLists.records xs := by
  exact List.mem_product.mpr ⟨List.mem_finRange _,List.mem_finRange _⟩



































end ThreeSum.RawAKeyLists

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Completeness of the physical wanted-record array

The pair array produced by the selected-offset join covers every original
guarded wanted label. Conversely every stored pair selects such a label.
These statements concern the actual emitted array, including duplicate
integer keys at different source positions.
-/

namespace ThreeSum.WantedRecordCoverage
open _root_.ThreeSum.WantedRecordCoverage


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.WantedRecordOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000

theorem label_surjective {xs : List ℤ} {h J : ℕ}
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (Fin xs.length)) :
    ∃ i j, ∃ hi : i < 3*xs.length,
      j < _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J ∧ _root_.ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder.label h J i j hi=w := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp (_root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists.mem_records xs (w.2.1,w.1))
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.mem_globalRecords h J w.2.2)
  have hi' : i.val < 3*xs.length := by
    simpa only [_root_.ThreeSum.RawAKeyLists.records_length] using i.isLt
  have hj' : j.val < _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J := by
    have hj0 : j.val < _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h^J := by
      simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.globalRecords_length'] using j.isLt
    exact hj0
  have hrec : (_root_.ThreeSum.RawAKeyLists.records xs).getD i.val (0,⟨0,_root_.ThreeSum.WantedRecordOrder.input_length_pos hi'⟩)=
      (w.2.1,w.1) := by
    simpa only [List.getD_eq_getElem _ _ i.isLt,List.get_eq_getElem] using hi
  rw [_root_.ThreeSum.WantedRecordOrder.records_getD hi'] at hrec
  have hposition := congrArg (fun r : Fin 3 × Fin xs.length => r.2) hrec
  have hlift := congrArg (fun r : Fin 3 × Fin xs.length => r.1) hrec
  dsimp only at hposition hlift
  have hout : _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeOriginal.output h J j.val=w.2.2 := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeOriginal.output,
      List.getD_eq_getElem _ _ j.isLt,List.get_eq_getElem] using hj
  refine ⟨i.val,j.val,hi',hj',?_⟩
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder.label
  rw [hposition,hlift,hout]





end ThreeSum.WantedRecordCoverage

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.WantedRecordCoverage

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.WantedRecordOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder
set_option maxHeartbeats 1400000
set_option maxRecDepth 7000
section

theorem ThreeSum1960614.Machine.ThreeSum.WantedRecordCoverage.output_complete__implementation_be8a384d63 {μ : ℕ → ℤ} {free M P h J : ℕ} {shift : ℤ} {xs : List ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.Output μ free M (_root_.ThreeSum.LightGuardedWanted.left P xs)
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right h J) (3*xs.length) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) shift)
    {w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (Fin xs.length)}
    (hw : w ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists.wanted M P xs h J shift) :
    ∃ slot i j, ∃ hi : i < 3*xs.length,
      slot < (μ free).toNat ∧ j < _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J ∧
      μ (_root_.ThreeSum.LightWantedSetup.pairBase free (3*xs.length) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) M+2*slot)=(i : ℤ) ∧
      μ (_root_.ThreeSum.LightWantedSetup.pairBase free (3*xs.length) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) M+2*slot+1)=(j : ℤ) ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder.label h J i j hi=w := by
  obtain ⟨i,j,hi,hj,he⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.WantedRecordCoverage.label_surjective w
  have hdiv := (_root_.ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder.mem_wanted_iff hi hj).mp (he.symm ▸ hw)
  rcases H with ⟨hcount,_,_,_,ps,hlen,_,hmem,hseg⟩
  have hp : (i,j) ∈ ps := (hmem i j).mpr ⟨hi,hj,hdiv⟩
  obtain ⟨k,hk⟩ := List.mem_iff_get.mp hp
  have hget : ps.getD k.val (0,0)=(i,j) := by
    simpa only [List.getD_eq_getElem _ _ k.isLt,List.get_eq_getElem] using hk
  have hread := _root_.ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder.segment_pair hseg k.isLt
  rw [hget] at hread
  refine ⟨k.val,i,j,hi,?_,hj,hread.1,hread.2,he⟩
  rw [hcount,Int.toNat_natCast,← hlen]
  exact k.isLt
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.WantedRecordCoverage.output_complete__implementation_be8a384d63) := (@ThreeSum1960614.Machine.ThreeSum.WantedRecordCoverage.output_complete__implementation_be8a384d63)

#print axioms solution
