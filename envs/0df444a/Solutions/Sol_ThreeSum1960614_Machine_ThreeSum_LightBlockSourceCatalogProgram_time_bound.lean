-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalogProgram.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:12:51.203228+00:00
-- url     : https://prove2.me/submissions/d09277b4-47fd-4273-9e6f-d8597ab3b8a8

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle028
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
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
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
import Mathlib.Data.Fintype.Fin
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
import Mathlib.Tactic.LinearCombination
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBlockSourceBatchProgram_time_bound
import Theorems.Thm_ThreeSum_LightSourceOccurrenceArray_time_bound

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightBlockSourceCatalogProgram
end ThreeSum.LightBlockSourceCatalogProgram
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalogProgram
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalogProgram
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalogProgram

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog
set_option maxHeartbeats 2200000
set_option maxRecDepth 16000
section

theorem ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalogProgram.time_bound__implementation_ed9bdf44fa {h J cut : ℕ} (hcut : cut ≤ J*(464*h)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.time h J cut ≤
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J+1)*_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalogProgram.factor h J*(_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut+1) := by
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchProgram.time_bound (count := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) hcut
  have hr := _root_.ThreeSum.LightSourceOccurrenceArray.time_bound (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) J
  have hr' : _root_.ThreeSum.LightSourceOccurrenceArray.time (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) J ≤
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J+1)*(300*(J+1)*(Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J+1)+2))*
        (_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut+1) := by
    calc
      _ ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J+1)*(300*(J+1)*(Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J+1)+2)) := by
        simpa only [mul_assoc,mul_comm,mul_left_comm] using hr
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
  have hconst : 400 ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J+1)*400*(_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut+1) := by
    calc
      _ ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J+1)*400 := by omega
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.time
  calc
    _ ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J+1)*(300*(J+1)*(Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J+1)+2))*
          (_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut+1)+
        (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J+1)*(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedProgram.factor h J+720)*
          (_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut+1)+
        (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J+1)*400*(_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut+1) :=
      Nat.add_le_add (Nat.add_le_add hr' hb) hconst
    _ = _ := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalogProgram.factor; ring
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalogProgram.time_bound__implementation_ed9bdf44fa) := (@ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalogProgram.time_bound__implementation_ed9bdf44fa)

#print axioms solution
