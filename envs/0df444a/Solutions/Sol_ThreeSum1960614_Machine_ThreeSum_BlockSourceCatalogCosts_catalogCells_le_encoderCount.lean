-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts.catalogCells_le_encoderCount
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:51:35.908681+00:00
-- url     : https://prove2.me/submissions/abb575f2-6239-4b16-a976-84c2a6ac38a0

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

namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockSourceCatalogCosts
end ThreeSum.BlockSourceCatalogCosts
namespace ThreeSum.BlockSourceSharing
end ThreeSum.BlockSourceSharing
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum.ReportingHostSuffixCosts
end ThreeSum.ReportingHostSuffixCosts
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts
end ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
end ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffixCosts
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffixCosts
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.TrimScales
end ThreeSum1960614.Machine.ThreeSum.TrimScales

namespace ThreeSum1960614.Machine

/-! # The actual local box construction is charged to the suffix binomial layer -/

namespace ThreeSum.ReportingHostSuffixCosts
open _root_.ThreeSum.ReportingHostSuffixCosts


open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open scoped _root_.BigOperators

theorem choose_le_cut {V j cut : ℕ} (hj : j ≤ cut) (hhalf : cut ≤ V/2) :
    V.choose j ≤ V.choose cut := by
  induction cut,hj using Nat.le_induction with
  | base => exact le_rfl
  | succ cut hj ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

theorem downsetCap_le_layer {V cut : ℕ} (hhalf : cut ≤ V/2) :
    _root_.ThreeSum.SubsetAddress.downsetCap V cut ≤ (cut+1)*V.choose cut := by
  have hcut : cut ≤ V := hhalf.trans (Nat.div_le_self _ _)
  simp only [_root_.ThreeSum.SubsetAddress.downsetCap,Nat.min_eq_left hcut,_root_.ThreeSum.SubsetAddress.layerOffset]
  calc
    _ ≤ ∑ _j ∈ Finset.range (cut+1), V.choose cut := by
      apply Finset.sum_le_sum
      intro j hj
      exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffixCosts.choose_le_cut (by have := Finset.mem_range.mp hj; omega) hhalf
    _ = _ := by simp

theorem downsetCap_add_one_le_layer {V cut : ℕ} (hhalf : cut ≤ V/2) :
    _root_.ThreeSum.SubsetAddress.downsetCap V cut+1 ≤ (V+2)*V.choose cut := by
  have hcut : cut ≤ V := hhalf.trans (Nat.div_le_self _ _)
  have hp := Nat.choose_pos hcut
  have hd := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffixCosts.downsetCap_le_layer hhalf
  have hm := Nat.mul_le_mul_right (V.choose cut) (Nat.succ_le_succ hcut)
  nlinarith









end ThreeSum.ReportingHostSuffixCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact sharing of source transforms and the encoder ledger

Source stages are indexed by a source band and an occurrence vector. The
output subset and the three-valued A lift do not enter the source function.
Compact table and zeta charges below match the existing `encoderCount`
without introducing a factor for all complete global outputs.
-/

namespace ThreeSum.BlockSourceSharing
open _root_.ThreeSum.BlockSourceSharing


open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds



















theorem downset_add_one_le_fullOutputs (n : ℕ) :
    _root_.ThreeSum.SubsetAddress.downsetCap (232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)+1 ≤ (232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+2)*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffixCosts.downsetCap_add_one_le_layer (by omega)













end ThreeSum.BlockSourceSharing

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact shared-bank dimensions and charge of the actual catalog

There are two stage families for each original band and occurrence vector.
The decoder and bank-loop overhead are included. Neither the number of
complete output subsets nor the three-valued query lift multiplies this
construction.
-/

namespace ThreeSum.BlockSourceCatalogCosts
open _root_.ThreeSum.BlockSourceCatalogCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout





theorem stride_add_two_le (W cut : ℕ) :
    _root_.ThreeSum.LightBlockSourceBatchLayout.stride W cut+2 ≤ (2*W+7)*(_root_.ThreeSum.SubsetAddress.downsetCap W cut+1) := by
  unfold _root_.ThreeSum.LightBlockSourceBatchLayout.stride _root_.ThreeSum.LightBlockSourceBatchLayout.family
  nlinarith



















end ThreeSum.BlockSourceCatalogCosts

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts

open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
section

theorem ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts.catalogCells_le_encoderCount__implementation_d507ac1747 (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts.catalogCells n ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)+2*(232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)+7)*(232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+2)*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n := by
  have hstride := _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts.stride_add_two_le (232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)
  have hJ : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)*(_root_.ThreeSum.SubsetAddress.downsetCap (232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)+1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hslot : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)+_root_.ThreeSum.LightBlockSourceBatchLayout.stride (232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)+2 ≤
      (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)+2*(232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)+7)*(_root_.ThreeSum.SubsetAddress.downsetCap (232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)+1) := by
    nlinarith
  have hd := _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.downset_add_one_le_fullOutputs n
  have he : _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n := by
    calc
      _ ≤ 2*(_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n) :=
        Nat.le_mul_of_pos_left _ (by omega)
      _ = _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount; ring
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts.catalogCells
  calc
    _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n*((_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)+2*(232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)+7)*
        ((232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+2)*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n)) :=
      Nat.mul_le_mul_left _ (hslot.trans (Nat.mul_le_mul_left _ hd))
    _ = (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)+2*(232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)+7)*(232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+2)*
        (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ he
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts.catalogCells_le_encoderCount__implementation_d507ac1747) := (@ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts.catalogCells_le_encoderCount__implementation_d507ac1747)

#print axioms solution
