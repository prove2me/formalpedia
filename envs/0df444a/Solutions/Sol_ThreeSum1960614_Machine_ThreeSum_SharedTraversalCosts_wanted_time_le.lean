-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.wanted_time_le
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:55:51.363373+00:00
-- url     : https://prove2.me/submissions/2275225a-2b0b-4e61-a151-e2dbf088ef00

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle029
import Definitions.Def_ThreeSum1960614_Machine_Bundle030
import Definitions.Def_ThreeSum1960614_Machine_Bundle031
import Definitions.Def_ThreeSum1960614_Machine_Bundle032
import Definitions.Def_ThreeSum1960614_Machine_Bundle033
import Definitions.Def_ThreeSum1960614_Machine_Bundle034
import Definitions.Def_ThreeSum1960614_Machine_Bundle035
import Definitions.Def_ThreeSum1960614_Machine_Bundle036
import Definitions.Def_ThreeSum1960614_Machine_Bundle037
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
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_RawReporting_partitionWord_length
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_RawReporting_word_children
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_ReportingHostMasks_localChildren_mem
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_ReportingHostTerminalFrontier_frontier_time_le
import Theorems.Thm_ThreeSum_ReportingHostMasks_blockSet_localRow
import Theorems.Thm_ThreeSum_Reporting_frontier_length_le_mass

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
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostFrontier
end ThreeSum.ReportingHostFrontier
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.SharedTraversalCosts
end ThreeSum.SharedTraversalCosts
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
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
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
end ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier
end ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
end ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
namespace ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts
end ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

namespace ThreeSum1960614.Machine

/-!
# Query-coordinate lists and weighted subset semantics

The coordinate list has one entry per set bit of the query. Its powers
form a compact weight table for the output-sensitive enumeration routine.
-/

namespace ThreeSum.QueryCoordinates
open _root_.ThreeSum.QueryCoordinates


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open scoped _root_.BigOperators





































theorem setLayer_nodup (xs : List ℕ) (hn : xs.Nodup) (k : ℕ) :
    (_root_.ThreeSum.QueryCoordinates.setLayer xs k).Nodup := by
  apply (List.nodup_sublistsLen k hn).map_on
  intro a ha b hb he
  have ha' := (List.mem_sublistsLen.mp ha).1
  have hb' := (List.mem_sublistsLen.mp hb).1
  apply (hn.perm_iff_eq_of_sublist ha' hb').mp
  exact List.perm_of_nodup_nodup_toFinset_eq (hn.sublist ha') (hn.sublist hb') he



















theorem missingSets_nodup {W : ℕ} (Q : Finset (Fin W)) (k : ℕ) :
    (_root_.ThreeSum.QueryCoordinates.missingSets Q k).Nodup := by
  unfold _root_.ThreeSum.QueryCoordinates.missingSets
  apply (_root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.setLayer_nodup _ (List.nodup_reverse.mpr (_root_.ThreeSum.QueryCoordinates.positions_nodup Q W)) k).map_on
  intro a ha b hb he
  have has := (_root_.ThreeSum.QueryCoordinates.mem_setLayer _ (List.nodup_reverse.mpr (_root_.ThreeSum.QueryCoordinates.positions_nodup Q W)) _ _).mp ha
  have hbs := (_root_.ThreeSum.QueryCoordinates.mem_setLayer _ (List.nodup_reverse.mpr (_root_.ThreeSum.QueryCoordinates.positions_nodup Q W)) _ _).mp hb
  rw [List.toFinset_reverse,_root_.ThreeSum.QueryCoordinates.positions_toFinset] at has hbs
  have h := congrArg _root_.ThreeSum.SubsetAddress.natPositions he
  rw [_root_.ThreeSum.QueryCoordinates.decode_maskOf (has.1.trans (_root_.ThreeSum.SubsetAddress.natPositions_subset Q)),
      _root_.ThreeSum.QueryCoordinates.decode_maskOf (hbs.1.trans (_root_.ThreeSum.SubsetAddress.natPositions_subset Q))] at h
  exact h





end ThreeSum.QueryCoordinates

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























theorem globalChildren_nodup {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :
    (_root_.ThreeSum.ReportingHostMasks.globalChildren i Q h).Nodup := _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.missingSets_nodup _ _





theorem localChildren_nodup {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :
    (_root_.ThreeSum.ReportingHostMasks.localChildren i Q h).Nodup := by
  apply (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.globalChildren_nodup i Q h).map_on
  intro S hS T hT he
  have hs := (_root_.ThreeSum.QueryCoordinates.missingSets_mem _ _ _).mp hS
  have ht := (_root_.ThreeSum.QueryCoordinates.missingSets_mem _ _ _).mp hT
  rw [← _root_.ThreeSum.ReportingHostMasks.blockSet_localRow i Q hs.1,← _root_.ThreeSum.ReportingHostMasks.blockSet_localRow i Q ht.1,he]



























end ThreeSum.ReportingHostMasks

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Coverage and raw-mass charging in the machine's actual child order

The output-sensitive enumerator uses its recursive coordinate order. The
reporting tree is instantiated with that exact order here; its positive
frontiers retain the original incidences and their multiplicities.
-/

namespace ThreeSum.ReportingHostFrontier
open _root_.ThreeSum.ReportingHostFrontier


open _root_.Finset
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum.ReportingHostMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open scoped _root_.BigOperators



theorem mem_children_iff {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (k : ℕ)
    (S : Finset (Fin (464*h))) : S ∈ _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.children q k ↔ S ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.children q k := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.children _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.children
  split
  · exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.localChildren_mem _ _ _ _
  · rfl

theorem children_nodup {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (k : ℕ) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.children q k).Nodup := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.children
  split
  · exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.localChildren_nodup _ _ _
  · exact List.nodup_nil



section Indices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]



theorem word_children {h J : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ)) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)
    (r : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ) (hr : r ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.domain I w) (j : ℕ) (hj : j < J) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.word r)[j]'(by rw [_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.word,_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.partitionWord_length]; exact hj) ∈ _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.children w.2.2 j :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.mem_children_iff _ _ _).mpr (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.word_children I w r hr j hj)





theorem frontier_length_le_domain {h J k : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (hk : k ≤ J) : (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w k).length ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.domain I w).card := by
  have h := _root_.ThreeSum.Reporting.frontier_length_le_mass (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.domain I w) _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.word (fun _ => 1)
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.children w.2.2) (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery I w) J k
    (fun r _ => _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.partitionWord_length r.2.1) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.word_children I w)
    (fun _ _ _ => rfl) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.children_nodup w.2.2) hk
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier,Finset.sum_const,smul_eq_mul,mul_one] using h

















end Indices

end ThreeSum.ReportingHostFrontier

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact physical frontier slots and a capacity computed from root raw mass -/

namespace ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum.ReportingHostFrontierLayout


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum.ReportingHostMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false




















variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]



theorem rootMass_eq {h J : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ)) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass I w=(_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.domain I w).card := by
  simp [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass,_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery,_root_.ThreeSum.Reporting.mass,_root_.ThreeSum.Subset.fiberMass]






























end ThreeSum.ReportingHostFrontierLayout

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Cost of the executed positive-frontier traversal

The expensive expansion remains multiplied by the number of actual positive
parents. Empty frontiers pay only the fixed level overhead. The terminal
scan is charged to the exact original bucket products, and the dense guard
removes this proportional charge from the branch which has already exceeded
the threshold.
-/

namespace ThreeSum.SharedTraversalCosts
open _root_.ThreeSum.SharedTraversalCosts


open _root_.Finset
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
open scoped _root_.BigOperators

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false







variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem levels_time_eq {h J : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (D : ℕ → _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog) (K : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLevels.time I w D K = 30+1300*K+
      ∑ k ∈ range K, (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w k).length*
        (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveExpand.time h J k (D (k+1)).t+200) := by
  induction K with
  | zero => simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLevels.time]
  | succ K ih =>
      rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLevels.time,ih,sum_range_succ]
      unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep.time _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time
      omega

theorem levels_time_le {h J K : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (D : ℕ → _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog) (hK : K ≤ J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLevels.time I w D K ≤
      (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.domain I w).card*_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.levelUnit h J D K+1300*K+30 := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.levels_time_eq]
  have hs : (∑ k ∈ range K, (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w k).length*
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveExpand.time h J k (D (k+1)).t+200)) ≤
      (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.domain I w).card*_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.levelUnit h J D K := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.levelUnit
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    exact Nat.mul_le_mul_right _ (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier_length_le_domain I w
      ((mem_range.mp hk).le.trans hK))
  omega

theorem terminal_time_le {h J K NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (left right : ℕ → ℤ)
    (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i))
    (hvR : ∀ i : Fin NR, right i.val=c (eR i))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (hK : K ≤ J)
    (hkey : w.1 ∈ A ∧ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣
      (a w.1%(p : ℤ)+_root_.ThreeSum.RawIncidences.lift w.2.1*(p : ℤ)+shift)-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2) :
    let I := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalStored.time p shift left right NL NR I w K ≤
      (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.domain I w).card*(_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.charge h J K+240)+630 := by
  dsimp only
  let I := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.frontier_time_le p shift A B C a b c
    left right eL eR hvL hvR w hK hkey
  have hm := Nat.mul_le_mul_left (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.charge h J K)
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier_length_le_domain I w hK)
  change _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalStored.time p shift left right NL NR I w K ≤ _
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalStored.time
  change _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.time p shift left right NL NR w.2.2 K
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w K) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w K).length ≤
      240*(_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.domain I w).card+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.charge h J K*
        (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w K).length+30 at ht
  nlinarith

theorem search_time_le {h J K NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (left right : ℕ → ℤ)
    (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i))
    (hvR : ∀ i : Fin NR, right i.val=c (eR i))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (D : ℕ → _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog) (hK : K ≤ J)
    (hkey : w.1 ∈ A ∧ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣
      (a w.1%(p : ℤ)+_root_.ThreeSum.RawIncidences.lift w.2.1*(p : ℤ)+shift)-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2) :
    let I := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedSearch.time p shift left right NL NR I w D K ≤
      (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.domain I w).card*_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.searchUnit h J D K+1300*K+1160 := by
  dsimp only
  let I := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
  have hl := _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.levels_time_le I w D hK
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.terminal_time_le p shift A B C a b c left right eL eR hvL hvR w hK hkey
  change _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalStored.time p shift left right NL NR I w K ≤ _ at ht
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedSearch.time _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.searchUnit
  nlinarith



end ThreeSum.SharedTraversalCosts

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.SharedTraversalCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts

open _root_.Finset
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
open scoped _root_.BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
section

theorem ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.wanted_time_le__implementation_4108c526bf {h J K NL NR old threshold : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (left right : ℕ → ℤ)
    (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i))
    (hvR : ∀ i : Fin NR, right i.val=c (eR i))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (D : ℕ → _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog) (hK : K ≤ J)
    (hkey : w.1 ∈ A ∧ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣
      (a w.1%(p : ℤ)+_root_.ThreeSum.RawIncidences.lift w.2.1*(p : ℤ)+shift)-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2) :
    let I := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWanted.time p shift left right NL NR old threshold I w D K ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.initialUnit h J D K+
        (if threshold < old+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass I w then 0 else _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass I w*_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.searchUnit h J D K) := by
  dsimp only
  let I := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.search_time_le p shift A B C a b c left right eL eR hvL hvR w D hK hkey
  change _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedSearch.time p shift left right NL NR I w D K ≤
    (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.domain I w).card*_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.searchUnit h J D K+1300*K+1160 at hs
  change _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWanted.time p shift left right NL NR old threshold I w D K ≤
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.initialUnit h J D K+
      (if threshold < old+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass I w then 0 else _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass I w*_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.searchUnit h J D K)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWanted.time _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.initialUnit
  by_cases hg : threshold < old+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass I w
  · simp only [if_pos hg]
    omega
  · simp only [if_neg hg]
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass_eq]
    omega
end

end

theorem solution.{u_implementation_0,u_implementation_1,u_implementation_2} : type_of% (@ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.wanted_time_le__implementation_4108c526bf.{u_implementation_0,u_implementation_1,u_implementation_2}) := (@ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.wanted_time_le__implementation_4108c526bf.{u_implementation_0,u_implementation_1,u_implementation_2})

#print axioms solution
