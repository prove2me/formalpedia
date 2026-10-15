-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.prefix_time_le_dispatch_budget
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:06:22.021407+00:00
-- url     : https://prove2.me/submissions/557d3f2e-8897-4924-a55c-77d896f1f1a8

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle037
import Definitions.Def_ThreeSum1960614_Machine_Bundle038
import Definitions.Def_ThreeSum1960614_Machine_Bundle039
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
import Definitions.Def_ThreeSum1962Source_Bundle17
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
import Mathlib.Data.List.Dedup
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
import Mathlib.Data.Nat.Choose.Vandermonde
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankLevels_candidates_nonempty
import Theorems.Thm_ThreeSum_SharedTraversalCosts_prefix_time_le

local instance platformRadixNonzero_9cf7412f42 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Filter
end Filter
namespace Finset
end Finset
namespace Real
end Real
namespace Set
end Set
namespace ThreeSum
end ThreeSum
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedTraversalCosts
end ThreeSum.SharedTraversalCosts
namespace ThreeSum.Switch
end ThreeSum.Switch
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts
end ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.Switch
end ThreeSum1960614.Machine.ThreeSum.Switch

namespace ThreeSum1960614.Machine

/-!
# The executable integer quartic switch

The implementation scans integers `q ≤ r/2` and tests a cleared integer
inequality.  No real-number comparison, logarithm oracle, or unbounded
noncomputable search occurs in the definition.  For admissible depths the
candidate set is nonempty.  Minimality gives the exact `9/r` rounding error
needed by the certified box and entropy bounds.
-/

namespace ThreeSum.Switch
open _root_.ThreeSum.Switch


open _root_.Set
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales

set_option maxHeartbeats 0



















@[simp] theorem mem_candidates {J j r q : ℕ} :
    q ∈ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates J j r ↔ q ≤ r / 2 ∧ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.accepts J j r q := by
  simp [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates, Nat.lt_succ_iff]

theorem switchIndex_mem {J j r : ℕ} (h : (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates J j r).Nonempty) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex J j r ∈ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates J j r := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex, dif_pos h]
  exact Finset.min'_mem _ _



noncomputable section









































end
end ThreeSum.Switch

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The physical reporting catalogs use the certified traversal ledger

The switch in every retained catalog is the literal switch used by the
original finite ledger. This module connects the executed level and terminal
costs to those exact binomial terms, preserving the sum over levels.
-/

namespace ThreeSum.SharedTraversalCosts
open _root_.ThreeSum.SharedTraversalCosts


open _root_.Finset
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open scoped _root_.BigOperators

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000





theorem residual_eq (n k : ℕ) :
    _root_.ThreeSum.LightBlockQuery.residualSize (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n) k=_root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n k := rfl







theorem switch_le_half {n k : ℕ} (hk : k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Switch.actualSwitch n k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n k/2 := by
  have hn := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.candidates_nonempty
    (h := _root_.ThreeSum.SharedTraversalCosts.half n) (J := _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n) (k := k) hk
  have hm := (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.mem_candidates.mp (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex_mem hn)).1
  have hr : _root_.ThreeSum.SharedReportingBankLevels.residual (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n) k=_root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n k := by
    rw [← _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.residual_eq]
    unfold _root_.ThreeSum.SharedReportingBankLevels.residual _root_.ThreeSum.LightBlockQuery.residualSize
    ring
  rw [hr] at hm
  exact hm

theorem query_terms_pos {n k : ℕ} (hk : k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.queryTerms n k :=
  Nat.choose_pos ((_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.switch_le_half hk).trans (Nat.div_le_self _ _))

















open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open scoped _root_.Topology

noncomputable section











end
end ThreeSum.SharedTraversalCosts

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.SharedTraversalCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts

open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
section

theorem ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.prefix_time_le_dispatch_budget__implementation_4a3857aec3 {time mass : ℕ → ℕ} {c n k threshold count : ℕ}
    (hzero : time 0 ≤ 30)
    (hstep : ∀ i, time (i+1) ≤ time i+(_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scaledOverhead n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.queryTerms n 0+_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scalarOverhead c n)+
      if threshold < _root_.ThreeSum.SharedTraversalCosts.prefixMass mass i+mass i then 0 else
        mass i*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scaledOverhead n*(_root_.ThreeSum.CostLedger.microPartitions n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.allQueryTerms n+_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.terminalChoices n)))
    (hcount : count ≤ _root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.wantedBudget n)
    (hthreshold : threshold ≤ _root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.falseBudget k n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.representationBound n) :
    time count ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.dispatchBudget c k n := by
  have ht := _root_.ThreeSum.SharedTraversalCosts.prefix_time_le hzero hstep count
  have hq := Nat.le_mul_of_pos_right (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scalarOverhead c n)
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.query_terms_pos (n := n) (k := 0) (by omega))
  have hinit : _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scaledOverhead n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.queryTerms n 0+_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scalarOverhead c n ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.totalOverhead c n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.queryTerms n 0 := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.totalOverhead; nlinarith only [hq]
  have hwork : _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scaledOverhead n*(_root_.ThreeSum.CostLedger.microPartitions n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.allQueryTerms n+_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.terminalChoices n) ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.totalOverhead c n*(_root_.ThreeSum.CostLedger.microPartitions n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.allQueryTerms n+_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.terminalChoices n) :=
    Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  have hi := Nat.mul_le_mul hcount hinit
  have ha := Nat.mul_le_mul hthreshold hwork
  have hs := ht.trans (Nat.add_le_add (Nat.add_le_add_left hi 30) ha)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.dispatchBudget _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.initialCount _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.activeCount _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.terminalCount
  calc
    time count ≤ (30+_root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.wantedBudget n*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.totalOverhead c n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.queryTerms n 0)+
        _root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.falseBudget k n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.representationBound n*
          (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.totalOverhead c n*(_root_.ThreeSum.CostLedger.microPartitions n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.allQueryTerms n+_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.terminalChoices n)))+
        _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.totalOverhead c n*_root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.falseBudget k n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.representationBound n*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.terminalChoices n :=
      hs.trans (Nat.le_add_right _ _)
    _ = _ := by ring
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.prefix_time_le_dispatch_budget__implementation_4a3857aec3) := (@ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.prefix_time_le_dispatch_budget__implementation_4a3857aec3)

#print axioms solution
