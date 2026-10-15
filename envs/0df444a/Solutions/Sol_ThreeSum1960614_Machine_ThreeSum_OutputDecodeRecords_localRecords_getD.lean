-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localRecords_getD
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:03:52.230081+00:00
-- url     : https://prove2.me/submissions/ef9ab093-6dd4-49f4-96e0-b9ea40638c82

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
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
import Mathlib.Data.List.TakeDrop
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

namespace ThreeSum
end ThreeSum
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.OutputDecodeOrder
end ThreeSum.OutputDecodeOrder
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
end ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
namespace ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
end ThreeSum1960614.Machine.ThreeSum.RadixKeyLists

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords

open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.OutputDecodeOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
open _root_.ThreeSum.RadixKeyLists
open _root_.ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
section

theorem ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localRecords_getD__implementation_3926e3a8fc {h i : ℕ} (hi : i < _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.localRecords h).getD i (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.blockDefault h) =
      (⟨i/_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h,(Nat.div_lt_iff_lt_mul (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount_pos h)).mpr hi⟩,
        _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.layerRecord h ⟨i%_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h,Nat.mod_lt _ (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount_pos h)⟩) := by
  have hq : i/_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h < _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h := (Nat.div_lt_iff_lt_mul (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount_pos h)).mpr hi
  have hr : i%_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h < _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h := Nat.mod_lt _ (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount_pos h)
  have hidx : i/_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h*_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h+i%_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h=i := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod i (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h)
  have hocc : (List.finRange (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h)).getD (i/_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.blockDefault h).1 =
      ⟨i/_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h,hq⟩ := by
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_finRange] using hq)]
    apply Fin.ext
    simp
  have hmask : (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.layers h).getD (i%_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.blockDefault h).2 =
      _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.layerRecord h ⟨i%_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h,hr⟩ := by
    rw [List.getD_eq_getElem _ _ (by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.layers_length,_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount] using hr)]
    simp only [_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.layers,List.getElem_ofFn]
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.localRecords List.product
  conv_lhs => rw [← hidx]
  rw [_root_.ThreeSum.OutputDecodeOrder.getD_flatMap_uniform _ _ (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.layers_length,_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount])
    (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.blockDefault h).1 (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.blockDefault h) (by simpa only [List.length_finRange] using hq) hr]
  rw [hocc,_root_.List.getD_map_of_lt _ (by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.layers_length,_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount] using hr) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.blockDefault h).2 (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.blockDefault h),hmask]
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localRecords_getD__implementation_3926e3a8fc) := (@ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localRecords_getD__implementation_3926e3a8fc)

#print axioms solution
