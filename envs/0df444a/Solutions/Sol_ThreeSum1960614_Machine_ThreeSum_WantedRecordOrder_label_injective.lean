-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder.label_injective
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T08:58:43.718986+00:00
-- url     : https://prove2.me/submissions/9c6a22fa-caef-4bbd-a64e-af9fa2d0e2ae

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
import Theorems.Thm_ThreeSum_RadixKeyLists_tuples_nodup
import Theorems.Thm_ThreeSum_SubsetAddress_enumerateLayer_nodup

namespace Finset
end Finset
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
namespace ThreeSum.OutputDecodeOrder
end ThreeSum.OutputDecodeOrder
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSum.RawAKeyLists
end ThreeSum.RawAKeyLists
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.WantedRecordOrder
end ThreeSum.WantedRecordOrder
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
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
namespace ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
end ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
namespace ThreeSum1960614.Machine.ThreeSum.RawAKeyLists
end ThreeSum1960614.Machine.ThreeSum.RawAKeyLists
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
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



theorem layerRecord_injective (h : ℕ) : Function.Injective (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.layerRecord h) := by
  intro i j he
  apply Fin.ext
  exact _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph.setAt_injective i.isLt j.isLt (congrArg Subtype.val he)









theorem layers_nodup (h : ℕ) : (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.layers h).Nodup :=
  List.nodup_ofFn_ofInjective (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.layerRecord_injective h)







theorem localRecords_nodup (h : ℕ) : (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.localRecords h).Nodup :=
  (List.nodup_finRange _).product (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.layers_nodup h)













theorem globalRecords_nodup (h J : ℕ) : (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalRecords h J).Nodup := by
  apply ((_root_.ThreeSum.RadixKeyLists.tuples_nodup _ (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.localRecords_nodup h) J).attach).map
  intro xs ys he
  apply Subtype.ext
  have he' := congrArg List.ofFn he
  simpa only [_root_.ThreeSum.GlobalKeyEnumeration.ofFn_tupleOfList] using he'













end ThreeSum.GlobalKeyEnumeration

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.WantedRecordOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder

open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum.RawAKeyLists
open _root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists
open _root_.ThreeSum.OutputDecodeOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
section

theorem ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder.label_injective__implementation_8bd86ffa99 {xs : List ℤ} {h J i i' j j' : ℕ}
    (hi : i < 3*xs.length) (hi' : i' < 3*xs.length)
    (hj : j < _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) (hj' : j' < _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J)
    (he : _root_.ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder.label h J i j hi=_root_.ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder.label h J i' j' hi') : i=i' ∧ j=j' := by
  have hr : i%xs.length=i'%xs.length := congrArg (fun w => w.1.val) he
  have hq : i/xs.length=i'/xs.length := congrArg (fun w => w.2.1.val) he
  have ho := congrArg (fun w => w.2.2) he
  have hj0 : j < (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalRecords h J).length := by
    rwa [_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.globalRecords_length']
  have hj1 : j' < (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalRecords h J).length := by
    rwa [_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.globalRecords_length']
  have hget : (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalRecords h J).get ⟨j,hj0⟩=(_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalRecords h J).get ⟨j',hj1⟩ := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder.label,_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeOriginal.output,List.getD_eq_getElem _ _ hj0,
      List.getD_eq_getElem _ _ hj1,List.get_eq_getElem] using ho
  have hh := congrArg Fin.val ((_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalRecords_nodup h J).injective_get hget)
  refine ⟨?_,hh⟩
  have hi0 := Nat.div_add_mod i xs.length
  have hi1 := Nat.div_add_mod i' xs.length
  rw [hq,hr] at hi0
  omega
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder.label_injective__implementation_8bd86ffa99) := (@ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder.label_injective__implementation_8bd86ffa99)

#print axioms solution
