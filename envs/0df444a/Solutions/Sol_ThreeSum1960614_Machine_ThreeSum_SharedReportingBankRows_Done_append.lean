-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.Done.append
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:17:52.521851+00:00
-- url     : https://prove2.me/submissions/a8272766-7af1-4503-9bc2-4d499349dedb

import Aesop
import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle002
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
import Definitions.Def_ThreeSum1960614_Machine_Bundle033
import Definitions.Def_ThreeSum1960614_Machine_Bundle034
import Definitions.Def_ThreeSum1960614_Machine_Bundle035
import Definitions.Def_ThreeSum1960614_Machine_Bundle036
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
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_ThreeSum1962Source_Bundle16
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
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
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
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
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
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
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
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
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankData_Tables_of_window

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SharedReportingBankRows
end ThreeSum.SharedReportingBankRows
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

namespace ThreeSum1960614.Machine

/-!
# Exact compact layout for a shared reporting catalog cell

The local pair and prefix counts are retained exactly. Each cell reserves
the two prefix arrays, its pointer row, all suffix boxes, the sorted index,
and the polynomial scratch used by the existing constructor. Layout sums
are later computed by the bank setup loop.
-/

namespace ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum.SharedReportingBankLayout


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog

set_option maxHeartbeats 1400000
set_option maxRecDepth 9000



























theorem ordered (base h J k boxCut : ℕ) :
    base ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairL base h ∧ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairL base h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairR base h ∧ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairR base h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageL base h ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageL base h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageR base h k ∧ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageR base h k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers base h k ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers base h k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes base h k ∧ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes base h k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks base h J k boxCut ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks base h J k boxCut ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work base h J k boxCut ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work base h J k boxCut ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish base h J k boxCut := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageR,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageL,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairR,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairL]
  omega

theorem finish_add (base h J k boxCut : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish base h J k boxCut=base+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.cellSize h J k boxCut := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.cellSize _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageR _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageL _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairR _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairL
  omega



theorem index_end (base h J k boxCut : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.index base h J k boxCut+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work base h J k boxCut := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.index _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work
  omega















theorem levelOffset_step (h J : ℕ) (boxCut : ℕ → ℕ) (k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.levelOffset h J boxCut k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.levelOffset h J boxCut (k+1) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.levelOffset]
  omega

theorem levelOffset_mono (h J : ℕ) (boxCut : ℕ → ℕ) : Monotone (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.levelOffset h J boxCut) :=
  monotone_nat_of_le_succ (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.levelOffset_step h J boxCut)

theorem finish_level (base h J k : ℕ) (boxCut : ℕ → ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish (base+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.levelOffset h J boxCut k) h J k (boxCut k)=
      base+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.levelOffset h J boxCut (k+1) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish_add,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.levelOffset]
  omega

end ThreeSum.SharedReportingBankLayout

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact level layout and retention for one shared source pair -/

namespace ThreeSum.SharedReportingBankLevels
open _root_.ThreeSum.SharedReportingBankLevels


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData

set_option maxHeartbeats 1400000
































theorem baseAt_mono (base h J : ℕ) : Monotone (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J) := by
  intro i j hij
  exact Nat.add_le_add_left (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.levelOffset_mono h J (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J) hij) base

theorem finish_baseAt (base h J k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J k) h J k (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J k)=_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J (k+1) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish_level base h J k (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J)

theorem catalog_low (base h J k : ℕ) :
    base ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalogAt base h J k).indexBase ∧
    base ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalogAt base h J k).ptrBase ∧
    base ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalogAt base h J k).boxBase := by
  have ho := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.ordered (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J k) h J k (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J k)
  have hb : base ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J k := Nat.le_add_right _ _
  dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalogAt,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.catalog,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.index]
  omega

theorem catalog_end (base h J k : ℕ) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalogAt base h J k).indexBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J (k+1) ∧
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalogAt base h J k).ptrBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J (k+1) ∧
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalogAt base h J k).boxBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k*
      _root_.ThreeSum.LightReportingSuffixCatalog.stride ((J-k)*(464*h)) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J k) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J (k+1) := by
  have ho := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.ordered (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J k) h J k (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J k)
  have hi := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.index_end (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J k) h J k (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J k)
  have hp : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J k) h k+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k=_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J k) h k := rfl
  have hm : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J k) h k+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k*
      _root_.ThreeSum.LightReportingSuffixCatalog.stride ((J-k)*(464*h)) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J k)=_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J k) h J k (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J k) := rfl
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.finish_baseAt]
  dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalogAt,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.catalog]
  omega





end ThreeSum.SharedReportingBankLevels

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact occurrence/B-band/C-band row order and retained catalog ownership -/

namespace ThreeSum.SharedReportingBankRows
open _root_.ThreeSum.SharedReportingBankRows


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum.SharedReportingBankLevels
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData

set_option maxHeartbeats 1800000







theorem digit_injective {n a b c d : ℕ} (hb : b < n) (hd : d < n)
    (he : a*n+b=c*n+d) : a=c ∧ b=d := by
  have hmod := congrArg (fun x => x%n) he
  have hbd : b=d := by simpa [Nat.add_mod,Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt hd] using hmod
  have hp : a*n=c*n := by omega
  exact ⟨Nat.eq_of_mul_eq_mul_right (by omega) hp,hbd⟩

theorem rank_injective {nb nc s i j s' i' j' : ℕ}
    (hi : i < nb) (hj : j < nc) (hi' : i' < nb) (hj' : j' < nc)
    (he : _root_.ThreeSum.SharedReportingBankRows.rank nb nc s i j=_root_.ThreeSum.SharedReportingBankRows.rank nb nc s' i' j') : s=s' ∧ i=i' ∧ j=j' := by
  have hinner := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.digit_injective hj hj' he
  have houter := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.digit_injective hi hi' hinner.1
  exact ⟨houter.1,houter.2,hinner.2⟩

theorem rank_lt {S nb nc s i j : ℕ} (hs : s < S) (hi : i < nb) (hj : j < nc) :
    _root_.ThreeSum.SharedReportingBankRows.rank nb nc s i j < _root_.ThreeSum.SharedReportingBankRows.pairs S nb nc := by
  have hx : s*nb+i < S*nb := calc
    _ < s*nb+nb := Nat.add_lt_add_left hi _
    _ = (s+1)*nb := by ring
    _ ≤ S*nb := Nat.mul_le_mul_right nb (by omega)
  calc
    _ < (s*nb+i)*nc+nc := Nat.add_lt_add_left hj _
    _ = (s*nb+i+1)*nc := by ring
    _ ≤ S*nb*nc := Nat.mul_le_mul_right nc (by omega)












theorem rowBase_next (base h J K q : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.rowBase base h J K q) h J K=_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.rowBase base h J K (q+1) := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.rowBase _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt
  ring
theorem rowBase_mono (base h J K : ℕ) : Monotone (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.rowBase base h J K) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _

theorem entry_of_later_block {h J k record nextRecord n low bound : ℕ} {μ ν : ℕ → ℤ}
    {D : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog} {hk : k ≤ J} {f g : Finset (Fin (J*(464*h))) → ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData.Entry μ record D hk f g) (heq : _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν bound nextRecord n)
    (hrecord : record+5 ≤ nextRecord) (hnext : nextRecord+n ≤ low)
    (hlow : low ≤ bound) (hindexLow : low ≤ D.indexBase)
    (hptrLow : low ≤ D.ptrBase) (hboxLow : low ≤ D.boxBase)
    (hindex : D.indexBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤ bound) (hptr : D.ptrBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤ bound)
    (hbox : D.boxBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k*_root_.ThreeSum.LightReportingSuffixCatalog.stride ((J-k)*(464*h)) D.boxCut ≤ bound) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData.Entry ν record D hk f g := by
  refine ⟨?_,H.tables.of_window (fun a ha hb => heq a ⟨hb,Or.inr (by omega)⟩)
    hindexLow hptrLow hboxLow hindex hptr hbox⟩
  intro i hi
  have hi' : i < 5 := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog.record,List.length_map,List.length_cons,List.length_nil] using hi
  exact (heq _ ⟨by omega,Or.inl (by omega)⟩).trans (H.header i hi)

theorem levels_of_later_row {μ ν : ℕ → ℤ} {record base h J K nextRecord nextBase : ℕ}
    {f g : Finset (Fin (J*(464*h))) → ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.Built μ record base h J K f g)
    (heq : _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν nextBase nextRecord (5*K))
    (hrecords : record+5*K ≤ nextRecord) (hnext : nextRecord+5*K ≤ base)
    (hpayload : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J K ≤ nextBase) : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.Built ν record base h J K f g := by
  intro k hk
  obtain ⟨hkJ,Hk⟩ := H k hk
  have hlow := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalog_low base h J k
  have hend := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalog_end base h J k
  have hbefore := (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt_mono base h J (show k+1 ≤ K by omega)).trans hpayload
  refine ⟨hkJ,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.entry_of_later_block Hk heq (by omega) hnext
    ((Nat.le_add_right _ _).trans hpayload) hlow.1 hlow.2.1 hlow.2.2
    (hend.1.trans hbefore) (hend.2.1.trans hbefore) (hend.2.2.trans hbefore)⟩







end ThreeSum.SharedReportingBankRows

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.SharedReportingBankRows
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum.SharedReportingBankLevels
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
set_option maxHeartbeats 1800000
section


theorem ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.Done.append__implementation_ae66d2aa72 {μ ν : ℕ → ℤ} {record base h J K NB NC g s i j q : ℕ}
    {fB fC : ℕ → ℤ} {p shift : ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.Done μ record base h J K NB NC g q fB fC p shift)
    (hs : s < _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (hi : i < _root_.ThreeSum.BandPartition.size NB g)
    (hj : j < _root_.ThreeSum.BandPartition.size NC g)
    (hq : q=_root_.ThreeSum.SharedReportingBankRows.rank (_root_.ThreeSum.BandPartition.size NB g) (_root_.ThreeSum.BandPartition.size NC g) s i j)
    (Hnew : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.Built ν (_root_.ThreeSum.SharedReportingBankRows.rowRecord record K q) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.rowBase base h J K q) h J K
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource p (_root_.ThreeSum.SourceBandPartition.source NB g i) (fun t : Fin NB => fB t.val) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder.representative h J s))
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource p shift (_root_.ThreeSum.SourceBandPartition.source NC g j) (fun t : Fin NC => fC t.val) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder.representative h J s)))
    (heq : _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.rowBase base h J K q) (_root_.ThreeSum.SharedReportingBankRows.rowRecord record K q) (5*K))
    (hslab : record+5*K*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.total h J NB NC g ≤ base) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.Done ν record base h J K NB NC g (q+1) fB fC p shift := by
  have hqLt : q < _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.total h J NB NC g := by rw [hq]; exact _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.rank_lt hs hi hj
  have hmeta := Nat.mul_le_mul_left (5*K) (show q+1 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.total h J NB NC g by omega)
  have hnext : _root_.ThreeSum.SharedReportingBankRows.rowRecord record K q+5*K ≤ base := by unfold _root_.ThreeSum.SharedReportingBankRows.rowRecord; nlinarith
  intro s' hs' i' hi' j' hj' hr
  rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | hr
  · have Hold := H s' hs' i' hi' j' hj' hr
    have hm := Nat.mul_le_mul_left (5*K) (show
      _root_.ThreeSum.SharedReportingBankRows.rank (_root_.ThreeSum.BandPartition.size NB g) (_root_.ThreeSum.BandPartition.size NC g) s' i' j'+1 ≤ q by omega)
    apply _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.levels_of_later_row Hold heq
    · unfold _root_.ThreeSum.SharedReportingBankRows.rowRecord
      nlinarith
    · exact hnext.trans (Nat.le_add_right _ _)
    · rw [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.rowBase_next]
      exact _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.rowBase_mono base h J K (by omega)
  · have hh := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.rank_injective hi' hj' hi hj (hr.trans hq)
    rcases hh with ⟨rfl,rfl,rfl⟩
    simpa only [← hq] using Hnew
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.Done.append__implementation_ae66d2aa72) := (@ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.Done.append__implementation_ae66d2aa72)

#print axioms solution
