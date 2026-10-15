-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.frontier_time_le
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:31:12.658314+00:00
-- url     : https://prove2.me/submissions/7e0e0739-03df-45af-8e9f-b868c5c3f4c2

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
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_BlockForced_completed_bucket_sum
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_RawPrefixCounts_prefixQuery_eq_bucketPrefixMass
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_ReportingHostFrontier_mem_frontier_iff
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_ReportingHostTerminalChoices_mem_choices
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_StoredReporting_positivePrefix_valid
import Theorems.Thm_ThreeSum_ReportingHostMasks_blockSet_localRow
import Theorems.Thm_ThreeSum_Reporting_frontier_nodup

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
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightReportingBucketTest
end ThreeSum.LightReportingBucketTest
namespace ThreeSum.LightReportingLeafBatch
end ThreeSum.LightReportingLeafBatch
namespace ThreeSum.LightReportingTerminalMasks
end ThreeSum.LightReportingTerminalMasks
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightSourceBucketSelect
end ThreeSum.LightSourceBucketSelect
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostBlockBucketTest
end ThreeSum.ReportingHostBlockBucketTest
namespace ThreeSum.ReportingHostBucketTest
end ThreeSum.ReportingHostBucketTest
namespace ThreeSum.ReportingHostFrontier
end ThreeSum.ReportingHostFrontier
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.ReportingHostPositive
end ThreeSum.ReportingHostPositive
namespace ThreeSum.ReportingHostTerminalBatch
end ThreeSum.ReportingHostTerminalBatch
namespace ThreeSum.ReportingHostTerminalChoices
end ThreeSum.ReportingHostTerminalChoices
namespace ThreeSum.ReportingHostTerminalCosts
end ThreeSum.ReportingHostTerminalCosts
namespace ThreeSum.ReportingHostTerminalFrontier
end ThreeSum.ReportingHostTerminalFrontier
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.Subset
end ThreeSum.Subset
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
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
end ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingBucketTest
end ThreeSum1960614.Machine.ThreeSum.LightReportingBucketTest
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingLeafBatch
end ThreeSum1960614.Machine.ThreeSum.LightReportingLeafBatch
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
end ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect
end ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
end ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalGraph
end ThreeSum1960614.Machine.ThreeSum.LocalGraph
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
end ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest
end ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest
end ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier
end ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
end ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch
end ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices
end ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalCosts
end ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalCosts
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier
end ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier
namespace ThreeSum1960614.Machine.ThreeSum.SourceBuckets
end ThreeSum1960614.Machine.ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum.Subset
end ThreeSum1960614.Machine.ThreeSum.Subset
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





































theorem join_card {J L : ℕ} (I : Finset (Fin J)) (u : Fin J → Finset (Fin L)) :
    (_root_.ThreeSum.BlockRows.join I u).card = ∑ i ∈ I, (u i).card := Finset.card_sigma _ _

theorem join_card_of_balance {J L h : ℕ} (I : Finset (Fin J))
    (u : Fin J → Finset (Fin L)) (hu : ∀ i ∈ I, (u i).card = h) :
    (_root_.ThreeSum.BlockRows.join I u).card = I.card * h := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_card]
  simp only [Finset.sum_congr rfl hu, Finset.sum_const, Nat.nsmul_eq_mul]







@[simp] theorem mem_prefixIndices {J k : ℕ} {i : Fin J} :
    i ∈ _root_.ThreeSum.BlockRows.prefixIndices J k ↔ i.val < k := by simp [_root_.ThreeSum.BlockRows.prefixIndices]



end ThreeSum.BlockRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Costed signed residue conversion

This loop uses the benchmark's proved division-free remainder procedure.
Its sign argument supports either an ordinary histogram or a histogram of
the negated original integers. All source multiplicities are retained.
The logarithmic scratch region is reused for each input element.
-/

namespace ThreeSum.LightResidues
open _root_.ThreeSum.LightResidues


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



theorem residue_cast {p : ℕ} (hp : 0 < p) (c x : ℤ) :
    (_root_.ThreeSum.LightResidues.residue p c x : ℤ) = (c * x) % (p : ℤ) := by
  apply Int.toNat_of_nonneg
  exact Int.emod_nonneg _ (by exact_mod_cast hp.ne')

















end ThreeSum.LightResidues

end ThreeSum1960614.Machine

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















@[simp] theorem positions_length {W : ℕ} (Q : Finset (Fin W)) :
    (_root_.ThreeSum.QueryCoordinates.positions Q W).length = Q.card := by
  rw [← List.toFinset_card_of_nodup (_root_.ThreeSum.QueryCoordinates.positions_nodup Q W),_root_.ThreeSum.QueryCoordinates.positions_toFinset,_root_.ThreeSum.SubsetAddress.natPositions_card]



















@[simp] theorem setLayer_length (xs : List ℕ) (k : ℕ) :
    (_root_.ThreeSum.QueryCoordinates.setLayer xs k).length = xs.length.choose k := by
  simp [_root_.ThreeSum.QueryCoordinates.setLayer,List.length_sublistsLen]

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

@[simp] theorem missingSets_length {W : ℕ} (Q : Finset (Fin W)) (k : ℕ) :
    (_root_.ThreeSum.QueryCoordinates.missingSets Q k).length = Q.card.choose k := by
  simp [_root_.ThreeSum.QueryCoordinates.missingSets]



end ThreeSum.QueryCoordinates

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact subset identities used by the proposed 3SUM algorithm

This module proves the algebraic identities, rather than taking the claimed
algorithm or its running time as an assumption.  `zeta` is the ordinary finite
subset sum; `mobius` is its signed inverse.  The fixed-cardinality specialization
is the identity used by the repeated histogram construction.
-/

namespace ThreeSum.Subset
open _root_.ThreeSum.Subset


open scoped _root_.BigOperators

variable {α : Type*} [DecidableEq α]



































/-! ## Stored partial zeta stages -/





























/-! ## Prefix reporting mass -/



/-- Refinement into all allowed next labels preserves the original weighted
mass, including multiplicity. This is a finite-sum identity, not a bound assumed
from the proposed 3SUM algorithm. -/
theorem fiberMass_conservation {β γ : Type*} [DecidableEq γ]
    (domain : Finset β) (labels : Finset γ) (label : β → γ) (weight : β → ℕ)
    (hlabels : ∀ p ∈ domain, label p ∈ labels) :
    (∑ value ∈ labels, _root_.ThreeSum.Subset.fiberMass domain label weight value) =
      ∑ p ∈ domain, weight p := by
  exact Finset.sum_fiberwise_of_maps_to hlabels weight







end ThreeSum.Subset

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











@[simp] theorem indexSet_card {J L : ℕ} (S : Finset (_root_.ThreeSum.BlockRows.Coord J L)) :
    (_root_.ThreeSum.BlockIndex.indexSet S).card = S.card := Finset.card_map _



@[simp] theorem index_unindex {J L : ℕ} (S : Finset (Fin (J*L))) :
    _root_.ThreeSum.BlockIndex.indexSet (_root_.ThreeSum.BlockIndex.unindexSet (J := J) (L := L) S) = S := by
  ext c
  simp [_root_.ThreeSum.BlockIndex.unindexSet,_root_.ThreeSum.BlockIndex.indexSet]



















end ThreeSum.BlockIndex

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original-input residue keys with a carry offset

The source histogram uses `(x % p + shift) % m`, with two independently
chosen moduli. This procedure computes both remainders from each original
signed input and retains every incidence, including duplicate values.
-/

namespace ThreeSum.LightSourceResidues
open _root_.ThreeSum.LightSourceResidues


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000



theorem key_cast {p m : ℕ} (hm : 0 < m) (shift x : ℤ) :
    (_root_.ThreeSum.LightSourceResidues.key p m shift x : ℤ) = (x % (p : ℤ) + shift) % (m : ℤ) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hm.ne'))













variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}











end ThreeSum.LightSourceResidues

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact stored-subset queries for the concrete reporting tree

A malformed prefix has zero mass. Every valid prefix is evaluated by the
stored suffix-zeta stages and the signed subset formula. These values are
proved to equal the natural raw-incidence fiber counts at every tree node.
-/

namespace ThreeSum.StoredReporting
open _root_.ThreeSum.StoredReporting


set_option maxRecDepth 8000

open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced

section

private theorem private_4ccb502193_ofFn_take_eq_iff {α : Type*} {J k : ℕ} (f g : Fin J → α) :
    (List.ofFn f).take k = (List.ofFn g).take k ↔ ∀ i : Fin J, i.val < k → f i = g i := by
  constructor
  · intro he i hi
    have hh := congrArg (fun xs => xs[i.val]?) he
    simpa only [List.getElem?_take_of_lt hi, List.getElem?_ofFn, dif_pos i.isLt,
      Option.some.injEq] using hh
  · intro h
    apply List.ext_getElem?
    intro i
    by_cases hi : i < k
    · rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt hi]
      by_cases hiJ : i < J
      · simp only [List.getElem?_ofFn, dif_pos hiJ, h ⟨i, hiJ⟩ hi]
      · simp only [List.getElem?_ofFn, dif_neg hiJ]
    · simp only [List.getElem?_take, hi, ite_false]
end






theorem take_prefixRows {J L k : ℕ} (pre : List (Finset (Fin L)))
    (hp : pre.length = k) (hk : k ≤ J) : (List.ofFn (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre)).take k = pre := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < k
  · have hiJ : i < J := hi.trans_le hk
    have hip : i < pre.length := hp ▸ hi
    simp only [List.getElem?_take_of_lt hi, List.getElem?_ofFn, dif_pos hiJ, _root_.ThreeSum.StoredReporting.prefixRows,
      List.getElem?_eq_getElem hip, Option.getD_some]
  · rw [List.getElem?_take_eq_none (Nat.le_of_not_lt hi),
      List.getElem?_eq_none (by omega)]

theorem completions_eq_completedTuples {h J k : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (u : Fin J → Finset (Fin (464 * h))) :
    _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.completions q k ((List.ofFn u).take k) = _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.completedTuples q (_root_.ThreeSum.BlockRows.prefixIndices J k) u := by
  ext t
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.completions, _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.completedTuples, Finset.mem_filter, Finset.mem_univ, true_and,
    _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.partitionWord, _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.private_4ccb502193_ofFn_take_eq_iff, _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_prefixIndices]





section Indices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]























end Indices

end ThreeSum.StoredReporting

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact bridge from row-major machine masks to the block reporting query

The explicit coordinate equivalence sends the remaining blocks to a
contiguous suffix. Transport of finite subset sums identifies the machine's
Möbius value with the concrete forced-prefix count used by reporting.
-/

namespace ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.BlockIndexedQuery


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open scoped _root_.BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

@[simp] theorem prefixIndices_card {J k : ℕ} (hk : k ≤ J) :
    (_root_.ThreeSum.BlockRows.prefixIndices J k).card = k := by
  simpa only [_root_.ThreeSum.BlockRows.prefixIndices,Nat.min_eq_right hk] using (Fin.card_filter_val_lt (n := J) (m := k))























theorem querySet_card {J L h k : ℕ} (hk : k ≤ J) (Q : Fin J → Finset (Fin L))
    (hQ : ∀ i, (Q i).card = 2*h) : (_root_.ThreeSum.BlockIndexedQuery.querySet k Q).card = (J-k)*(2*h) := by
  rw [_root_.ThreeSum.BlockIndexedQuery.querySet,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.indexSet_card,_root_.ThreeSum.BlockForced.remaining,_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_card_of_balance _ _ (fun i _ => hQ i),
    Finset.card_compl,Fintype.card_fin,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.prefixIndices_card hk]







section Histograms

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]



















end Histograms

end ThreeSum.BlockIndexedQuery

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original-input histograms give the exact independently trimmed sources

The histogram keys retain the first modular reduction and the signed carry
offset. Looking up the endpoint's final residue therefore counts precisely
the original divisibility condition in `BlockEncoding`. An explicit finite
enumeration accounts for every original input incidence once.
-/

namespace ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.BlockSourceEncoding


open _root_.Finset
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightSourceResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
open scoped _root_.BigOperators

set_option maxHeartbeats 1000000

theorem key_eq_iff {p m : ℕ} (hm : 0 < m) (shift x endpoint : ℤ) :
    _root_.ThreeSum.LightSourceResidues.key p m shift x = _root_.ThreeSum.LightResidues.residue m 1 endpoint ↔
      (m : ℤ) ∣ x % (p : ℤ) + shift - endpoint := by
  rw [← Int.natCast_inj, _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.key_cast hm, _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_cast hm, one_mul,
    Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero]

theorem count_eq_sum {p m : ℕ} (hm : 0 < m) (shift endpoint : ℤ)
    (values : ℕ → ℤ) (n : ℕ) :
    _root_.ThreeSum.LightHistogram.count (fun i => _root_.ThreeSum.LightSourceResidues.key p m shift (values i))
      (_root_.ThreeSum.LightResidues.residue m 1 endpoint) n =
        ∑ i ∈ range n, if (m : ℤ) ∣ values i % (p : ℤ) + shift - endpoint
          then 1 else 0 := by
  unfold _root_.ThreeSum.LightHistogram.count
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.key_eq_iff hm]

theorem count_eq_sum_of_equiv {β : Type*} [DecidableEq β]
    {p m n : ℕ} (hm : 0 < m) (shift endpoint : ℤ)
    (B : Finset β) (b : β → ℤ) (values : ℕ → ℤ)
    (e : Fin n ≃ B) (hvalues : ∀ i : Fin n, values i.val = b (e i)) :
    _root_.ThreeSum.LightHistogram.count (fun i => _root_.ThreeSum.LightSourceResidues.key p m shift (values i))
      (_root_.ThreeSum.LightResidues.residue m 1 endpoint) n =
        ∑ i ∈ B, if (m : ℤ) ∣ b i % (p : ℤ) + shift - endpoint then 1 else 0 := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.count_eq_sum hm,← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ i : B, if (m : ℤ) ∣ b i % (p : ℤ) + shift - endpoint then 1 else 0 := by
      apply Fintype.sum_equiv e
      intro i
      rw [hvalues i]
    _ = _ := Finset.sum_coe_sort B
      (fun i : β => if (m : ℤ) ∣ b i % (p : ℤ) + shift - endpoint then (1 : ℕ) else 0)



theorem modulus_pos (h J : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J := pow_pos (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h) J

@[simp] theorem modulus_cast (h J : ℕ) : (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J : ℤ) = _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus,Nat.cast_pow]

section OriginalSources

variable {β : Type*} [DecidableEq β]

theorem leftWeights_eq_histogram {h J n : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (p : ℕ)
    (B : Finset β) (b : β → ℤ) (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h)))
    (values : ℕ → ℤ) (e : Fin n ≃ B)
    (hvalues : ∀ i : Fin n, values i.val = b (e i)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftWeights o (p : ℤ) B b S =
      if _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.LeftAllowed o S then
        _root_.ThreeSum.LightHistogram.count (fun i => _root_.ThreeSum.LightSourceResidues.key p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) 0 (values i))
          (_root_.ThreeSum.LightResidues.residue (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) 1 (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointLeft o S)) n
      else 0 := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftWeights
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.count_eq_sum_of_equiv (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus_pos h J) 0 (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointLeft o S) B b values e hvalues]
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus_cast,add_zero]

theorem rightWeights_eq_histogram {h J n : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (p : ℕ) (shift : ℤ)
    (C : Finset β) (c : β → ℤ) (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h)))
    (values : ℕ → ℤ) (e : Fin n ≃ C)
    (hvalues : ∀ i : Fin n, values i.val = c (e i)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightWeights o (p : ℤ) shift C c S =
      if _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.RightAllowed o S then
        _root_.ThreeSum.LightHistogram.count (fun i => _root_.ThreeSum.LightSourceResidues.key p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) shift (values i))
          (_root_.ThreeSum.LightResidues.residue (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) 1 (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointRight o S)) n
      else 0 := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightWeights
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.count_eq_sum_of_equiv (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus_pos h J) shift (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointRight o S) C c values e hvalues]
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus_cast]

end OriginalSources

end ThreeSum.BlockSourceEncoding

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
# Actual independent bucket selection followed by original tuple testing

The host reads the two retained offset headers, applies each endpoint's
independent flag, and runs the exact original-value Cartesian scanner. Its
time is linear in the actual selected physical pair mass plus a constant.
-/

namespace ThreeSum.LightReportingBucketTest
open _root_.ThreeSum.LightReportingBucketTest


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram
open _root_.ThreeSum.LightSourceBucketSelect
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect
open _root_.ThreeSum.ReportingHostBucketTest
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000







variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





theorem time_eq (keyL keyR : ℕ → ℕ) (NL NR rL rR flagL flagR : ℕ) :
    _root_.ThreeSum.LightReportingBucketTest.time keyL keyR NL NR rL rR flagL flagR =
      240*(_root_.ThreeSum.LightSourceBucketSelect.countSelected keyL NL rL flagL*_root_.ThreeSum.LightSourceBucketSelect.countSelected keyR NR rR flagR)+700 := by
  unfold _root_.ThreeSum.LightReportingBucketTest.time _root_.ThreeSum.LightReportingBucketPairs.time
  ring

end ThreeSum.LightReportingBucketTest

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





theorem children_nodup {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (k : ℕ) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.children q k).Nodup := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.children
  split
  · exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.localChildren_nodup _ _ _
  · exact List.nodup_nil



section Indices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]







omit [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ] in
theorem frontier_nodup {h J : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (k : ℕ) : (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w k).Nodup :=
  _root_.ThreeSum.Reporting.frontier_nodup _ _ (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.children_nodup _) _



















end Indices

end ThreeSum.ReportingHostFrontier

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual terminal-candidate batch with a sum of physical pair charges

All endpoint and independent flag arrays are read from retained memory.
The recursion evaluates each candidate and retains a Boolean disjunction.
Its cost sums the actual leaf costs instead of multiplying a worst fiber
size by the number of candidates.
-/

namespace ThreeSum.LightReportingLeafBatch
open _root_.ThreeSum.LightReportingLeafBatch


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues
open scoped _root_.BigOperators

set_option maxHeartbeats 2600000
set_option maxRecDepth 10000







theorem time_eq_sum (keyL keyR flagL flagR : ℕ→ℕ) (NL NR Mo U : ℕ) (xL xR : ℕ→ℤ) (n : ℕ) :
    _root_.ThreeSum.LightReportingLeafBatch.time keyL keyR flagL flagR NL NR Mo U xL xR n=30+
      ∑ i∈range n, (_root_.ThreeSum.LightReportingLeaf.time keyL keyR NL NR Mo (flagL i) (flagR i) U (xL i) (xR i)+300) := by
  induction n with
  | zero => simp [_root_.ThreeSum.LightReportingLeafBatch.time]
  | succ n ih => simp only [_root_.ThreeSum.LightReportingLeafBatch.time,Finset.sum_range_succ,ih]; omega





variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}



end ThreeSum.LightReportingLeafBatch

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original endpoint semantics and exact Cartesian-test cost

The selected physical lengths are the original independently trimmed source
weights, after transport by the original-index enumeration. Thus the actual
tuple tester's pair charge is exactly the raw leaf weight.
-/

namespace ThreeSum.ReportingHostBlockBucketTest
open _root_.ThreeSum.ReportingHostBlockBucketTest


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.LightSourceResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightSourceBucketSelect
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect
open _root_.ThreeSum.ReportingHostBucketTest
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000









theorem selected_left_eq_weights {β : Type*} [DecidableEq β] {h J N : ℕ}
    (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (p : ℕ) (B : Finset β) (b : β→ℤ)
    (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h))) (v : ℕ→ℤ) (e : Fin N ≃ B)
    (hv : ∀ i : Fin N, v i.val=b (e i)) :
    _root_.ThreeSum.LightSourceBucketSelect.countSelected (fun i => _root_.ThreeSum.LightSourceResidues.key p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) 0 (v i)) N (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest.leftResidue o S) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest.leftFlag o S)=
      _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftWeights o (p : ℤ) B b S := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.leftWeights_eq_histogram o p B b S v e hv]
  unfold _root_.ThreeSum.LightSourceBucketSelect.countSelected _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest.leftFlag _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest.leftResidue
  by_cases hs : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.LeftAllowed o S <;> simp [hs]

theorem selected_right_eq_weights {γ : Type*} [DecidableEq γ] {h J N : ℕ}
    (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (p : ℕ) (shift : ℤ) (C : Finset γ) (c : γ→ℤ)
    (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h))) (v : ℕ→ℤ) (e : Fin N ≃ C)
    (hv : ∀ i : Fin N, v i.val=c (e i)) :
    _root_.ThreeSum.LightSourceBucketSelect.countSelected (fun i => _root_.ThreeSum.LightSourceResidues.key p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) shift (v i)) N (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest.rightResidue o S) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest.rightFlag o S)=
      _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightWeights o (p : ℤ) shift C c S := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.rightWeights_eq_histogram o p shift C c S v e hv]
  unfold _root_.ThreeSum.LightSourceBucketSelect.countSelected _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest.rightFlag _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest.rightResidue
  by_cases hs : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.RightAllowed o S <;> simp [hs]

theorem actual_time_eq {β γ : Type*} [DecidableEq β] [DecidableEq γ] {h J NL NR : ℕ}
    (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (p : ℕ) (shift : ℤ) (B : Finset β) (C : Finset γ)
    (b : β→ℤ) (c : γ→ℤ) (S T : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h))) (left right : ℕ→ℤ)
    (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j)) :
    _root_.ThreeSum.LightReportingBucketTest.time (fun i => _root_.ThreeSum.LightSourceResidues.key p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) 0 (left i))
      (fun j => _root_.ThreeSum.LightSourceResidues.key p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) shift (right j)) NL NR
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest.leftResidue o S) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest.rightResidue o T) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest.leftFlag o S) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest.rightFlag o T) =
        240*(_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftWeights o (p : ℤ) B b S*_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightWeights o (p : ℤ) shift C c T)+700 := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketTest.time_eq,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest.selected_left_eq_weights o p B b S left eL hvL,
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest.selected_right_eq_weights o p shift C c T right eR hvR]



end ThreeSum.ReportingHostBlockBucketTest

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact next-frontier order and raw-mass charges for the actual expansion

Gathering the stably selected child positions produces exactly the recursive
reporting frontier, including its original order and retained multiplicity.
-/

namespace ThreeSum.ReportingHostPositive
open _root_.ThreeSum.ReportingHostPositive


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
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
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier
open scoped _root_.BigOperators

set_option linter.unusedSectionVars false





theorem frontier_positive {α : Type*} (children : ℕ → List α) (query : ℕ → List α → ℕ)
    {k : ℕ} {pre : List α} (hp : pre ∈ _root_.ThreeSum.Reporting.frontier children query k) :
    0 < query k pre := by
  cases k with
  | zero =>
      simp only [_root_.ThreeSum.Reporting.frontier] at hp
      split at hp
      · have he : pre = [] := List.mem_singleton.mp hp
        simpa only [he] using ‹0 < query 0 []›
      · cases hp
  | succ k =>
      exact of_decide_eq_true (List.mem_filter.mp hp).2

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]







theorem frontier_valid {h J k : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (hk : k ≤ J) {pre : List (Finset (Fin (464*h)))}
    (hp : pre ∈ _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w k) : _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix w.2.2 k pre :=
  _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.positivePrefix_valid I w pre hk (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.frontier_positive _ _ hp)







end ThreeSum.ReportingHostPositive

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Finite terminal completions in the actual mask enumerator's order

At any valid reporting prefix, a full balanced endpoint needs exactly
`(J-k)*h` of the remaining query coordinates. Enumerating that one layer
contains every retained completion and costs no more than the terminal
Boolean-cube allowance. The selected bucket pair masses sum to at most the
unchanged original raw prefix count.
-/

namespace ThreeSum.ReportingHostTerminalChoices
open _root_.ThreeSum.ReportingHostTerminalChoices


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
open scoped _root_.BigOperators

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000



theorem choices_length {h J k : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (hk : k≤J) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices q k).length = ((J-k)*(2*h)).choose ((J-k)*h) := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices,List.length_map,_root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.missingSets_length]
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.querySet_card hk (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) (fun i => _root_.ThreeSum.LayerCounts.mem_vertices.mp (q i).2.property)]

theorem choices_length_le {h J k : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (hk : k≤J) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices q k).length ≤ 2^((J-k)*(2*h)) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices_length q hk]
  exact Nat.choose_le_two_pow _ _

theorem choices_nodup {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (k : ℕ) : (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices q k).Nodup := by
  apply (_root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.missingSets_nodup _ _).map
  intro S T he
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.index_unindex] using congrArg _root_.ThreeSum.BlockIndex.indexSet he





theorem completion_as_completed {h J k : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (pre : List (Finset (Fin (464*h)))) (hk : k≤J) (hp : _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix q k pre) :
    _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.completions q k pre=_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.completedTuples q (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum.StoredReporting.prefixRows pre) := by
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.completions_eq_completedTuples,_root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.take_prefixRows pre hp.1 hk]





variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]



theorem pairMass_sum_le_prefixQuery {h J k : ℕ} (P shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (pre : List (Finset (Fin (464*h)))) (hk : k≤J) (hp : _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix w.2.2 k pre)
    (hkey : w.1∈A ∧ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ (a w.1%P+_root_.ThreeSum.RawIncidences.lift w.2.1*P+shift)-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2) :
    ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices w.2.2 k).map (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.pairMass P shift B C b c w.2.2 k pre)).sum ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P shift (A ×ˢ (B ×ˢ C)) a b c) w k pre := by
  rw [← List.sum_toFinset _ (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices_nodup w.2.2 k)]
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.prefixQuery_eq_bucketPrefixMass,_root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.bucketPrefixMass,if_pos hkey,
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.completion_as_completed w.2.2 pre hk hp,
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.completed_bucket_sum P shift B C b c w.2.2 _ _
      (fun i hi => (hp.2 i (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_prefixIndices.mp hi)).1)]
  apply Finset.sum_le_sum_of_subset
  intro S hS
  exact Finset.mem_powerset.mpr ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.mem_choices w.2.2 k S).mp (List.mem_toFinset.mp hS)).1

end ThreeSum.ReportingHostTerminalChoices

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual terminal completion mask arrays

The existing exact coordinate enumerator is applied to the entire remaining
query set. It emits both full endpoint masks, so the independent endpoint
and bucket-test constructors can consume them without constructing tuples
or invoking an oracle. Every original retained completion occurs.
-/

namespace ThreeSum.LightReportingTerminalMasks
open _root_.ThreeSum.LightReportingTerminalMasks


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000











theorem choiceAt_eq_get {h J k i : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (hi : i<(_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices q k).length) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.choiceAt q k i=(_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices q k)[i] := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.choiceAt,List.getElem?_eq_getElem hi,Option.getD_some]







variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ}





end ThreeSum.LightReportingTerminalMasks

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Charging actual terminal scans to the original raw prefix mass

The actual independent bucket tester costs `240` per selected physical pair
plus `700` per terminal candidate. This file sums those exact verified costs
over the enumerator's unchanged order. It also proves conservation of raw
mass across the actual positive frontier at any partial depth.
-/

namespace ThreeSum.ReportingHostTerminalCosts
open _root_.ThreeSum.ReportingHostTerminalCosts


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.LightSourceResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
open scoped _root_.BigOperators

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

theorem sum_linear {δ : Type*} (xs : List δ) (f : δ→ℕ) (c d : ℕ) :
    (xs.map (fun x => c*f x+d)).sum=c*(xs.map f).sum+d*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih]; ring

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]



theorem actualTestWork_eq {h J NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (B : Finset β) (C : Finset γ) (b : β→ℤ) (c : γ→ℤ)
    (left right : ℕ→ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j))
    (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (k : ℕ) (pre : List (Finset (Fin (464*h)))) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalCosts.actualTestWork p shift left right NL NR q k pre =
      240*((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices q k).map (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.pairMass (p : ℤ) shift B C b c q k pre)).sum+700*(_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices q k).length := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalCosts.actualTestWork
  simp_rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest.actual_time_eq (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) p shift B C b c _ _ left right eL eR hvL hvR]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalCosts.sum_linear (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices q k) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.pairMass (p : ℤ) shift B C b c q k pre) 240 700

theorem actualTestWork_le {h J k NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (left right : ℕ→ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (pre : List (Finset (Fin (464*h)))) (hk : k≤J) (hp : _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix w.2.2 k pre)
    (hkey : w.1∈A ∧ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ (a w.1%(p : ℤ)+_root_.ThreeSum.RawIncidences.lift w.2.1*(p : ℤ)+shift)-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalCosts.actualTestWork p shift left right NL NR w.2.2 k pre ≤
      240*_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w k pre+
        700*2^((J-k)*(2*h)) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalCosts.actualTestWork_eq p shift B C b c left right eL eR hvL hvR]
  exact Nat.add_le_add
    (Nat.mul_le_mul_left 240 (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.pairMass_sum_le_prefixQuery (p : ℤ) shift A B C a b c w pre hk hp hkey))
    (Nat.mul_le_mul_left 700 (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices_length_le w.2.2 hk))

theorem frontier_mass {h J k : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ)) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (hk : k≤J) :
    ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w k).map (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery I w k)).sum=(_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.domain I w).card := by
  rw [← List.sum_toFinset _ (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier_nodup I w k)]
  change (∑ pre ∈ (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w k).toFinset,
    _root_.ThreeSum.Subset.fiberMass (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.domain I w) (fun r => (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.word r).take k) (fun _ => 1) pre)=(_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.domain I w).card
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.Subset.fiberMass_conservation]
  · simp
  · intro r hr
    apply List.mem_toFinset.mpr
    exact (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.mem_frontier_iff I w hk _).mpr
      ⟨r,(Finset.mem_filter.mp hr).1,(Finset.mem_filter.mp hr).2,rfl⟩



end ThreeSum.ReportingHostTerminalCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact original-encoding semantics and cost of the executed terminal batch

This is the specialization of the actual seven-procedure batch to the full
endpoint masks emitted at a valid partial prefix. The precise ordered
candidate sum is charged to raw prefix mass plus the terminal cube term.
-/

namespace ThreeSum.ReportingHostTerminalBatch
open _root_.ThreeSum.ReportingHostTerminalBatch


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.LightSourceResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
open _root_.ThreeSum.LightReportingTerminalMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
open scoped _root_.BigOperators

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false










theorem sum_choiceAt {h J k : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (hk : k≤J)
    (f : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h))→ℕ) :
    (∑ i∈range (_root_.ThreeSum.LightReportingTerminalMasks.count h J k), f (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.choiceAt q k i))=((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices q k).map f).sum := by
  rw [show _root_.ThreeSum.LightReportingTerminalMasks.count h J k=(_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices q k).length by exact (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices_length q hk).symm,Finset.sum_range]
  calc
    (∑ i : Fin (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices q k).length, f (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.choiceAt q k i.val)) =
        ∑ i : Fin (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices q k).length, f ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices q k)[i.val]) :=
      Finset.sum_congr rfl (fun i _ => congrArg f (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.choiceAt_eq_get q i.isLt))
    _ = _ := Fin.sum_univ_fun_getElem (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices q k) f

theorem time_eq {h J k : ℕ} (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (pre : List (Finset (Fin (464*h)))) (hk : k≤J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.time p shift left right NL NR q k pre=
      _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalCosts.actualTestWork p shift left right NL NR q k pre+
        _root_.ThreeSum.LightReportingTerminalMasks.count h J k*(2*_root_.ThreeSum.LightResidues.residueBudget (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J)+600)+30 := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.time
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLeafBatch.time_eq_sum]
  simp only [_root_.ThreeSum.LightReportingLeaf.time]
  have hsum := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.sum_choiceAt q hk (fun S =>
    _root_.ThreeSum.LightReportingBucketTest.time
      (fun i => _root_.ThreeSum.LightSourceResidues.key p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) 0 (left i)) (fun i => _root_.ThreeSum.LightSourceResidues.key p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) shift (right i)) NL NR
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest.leftResidue (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum.BlockForced.prefixLeft (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum.StoredReporting.prefixRows pre) ∪ S))
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest.rightResidue (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum.BlockForced.prefixRight (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) (_root_.ThreeSum.StoredReporting.prefixRows pre) ∪
        (_root_.ThreeSum.BlockForced.remaining (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) \ S)))
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest.leftFlag (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum.BlockForced.prefixLeft (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum.StoredReporting.prefixRows pre) ∪ S))
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest.rightFlag (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum.BlockForced.prefixRight (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) (_root_.ThreeSum.StoredReporting.prefixRows pre) ∪
        (_root_.ThreeSum.BlockForced.remaining (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) \ S))))
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,smul_eq_mul]
  change 30+(_+_+_+_)=_
  have hsum' : (∑ i∈range (_root_.ThreeSum.LightReportingTerminalMasks.count h J k),
      _root_.ThreeSum.LightReportingBucketTest.time
        (fun i => _root_.ThreeSum.LightSourceResidues.key p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) 0 (left i)) (fun i => _root_.ThreeSum.LightSourceResidues.key p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) shift (right i)) NL NR
        (_root_.ThreeSum.LightResidues.residue (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) 1 (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.endpointsLeft q k pre i))
        (_root_.ThreeSum.LightResidues.residue (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) 1 (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.endpointsRight q k pre i))
        (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.flagsLeft q k pre i) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.flagsRight q k pre i))=
      _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalCosts.actualTestWork p shift left right NL NR q k pre := hsum
  rw [hsum']
  ring

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem time_le {h J k NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (left right : ℕ→ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (pre : List (Finset (Fin (464*h)))) (hk : k≤J) (hp : _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix w.2.2 k pre)
    (hkey : w.1∈A ∧ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ (a w.1%(p : ℤ)+_root_.ThreeSum.RawIncidences.lift w.2.1*(p : ℤ)+shift)-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.time p shift left right NL NR w.2.2 k pre ≤
      240*_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w k pre+
        (2*_root_.ThreeSum.LightResidues.residueBudget (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J)+1300)*2^((J-k)*(2*h))+30 := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.time_eq p shift left right NL NR w.2.2 pre hk]
  have htest := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalCosts.actualTestWork_le p shift A B C a b c left right eL eR hvL hvR w pre hk hp hkey
  have hn : _root_.ThreeSum.LightReportingTerminalMasks.count h J k≤2^((J-k)*(2*h)) := Nat.choose_le_two_pow _ _
  have hmul := Nat.mul_le_mul_right (2*_root_.ThreeSum.LightResidues.residueBudget (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J)+600) hn
  nlinarith





end ThreeSum.ReportingHostTerminalBatch

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact terminal-prefix order, summed cost, and original completeness

The prefix batch consumes the actual retained frontier order. Every local
scan keeps its own selected-pair charge; their sum is bounded by the exact
original raw mass at the partial depth.
-/

namespace ThreeSum.ReportingHostTerminalFrontier
open _root_.ThreeSum.ReportingHostTerminalFrontier


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
open scoped _root_.BigOperators

set_option maxHeartbeats 2400000
set_option maxRecDepth 10000



theorem prefixAt_eq_get {h i : ℕ} (pres : List (List (Finset (Fin (464*h))))) (hi : i<pres.length) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.prefixAt pres i=pres[i] := by simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.prefixAt,List.getElem?_eq_getElem hi,Option.getD_some]









theorem time_all {h J : ℕ} (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (k : ℕ) (pres : List (List (Finset (Fin (464*h))))) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.time p shift left right NL NR q k pres pres.length=
      (pres.map (fun pre => _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminal.time p shift left right NL NR q k pre+300)).sum+30 := by
  have hsum (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.time p shift left right NL NR q k pres n=
      (∑ i∈range n, (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminal.time p shift left right NL NR q k (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.prefixAt pres i)+300))+30 := by
    induction n with
    | zero => simp [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.time]
    | succ n ih => simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.time,Finset.sum_range_succ,ih]; omega
  rw [hsum,Finset.sum_range]
  congr 1
  calc
    (∑ i : Fin pres.length, (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminal.time p shift left right NL NR q k (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.prefixAt pres i.val)+300)) =
        ∑ i : Fin pres.length, (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminal.time p shift left right NL NR q k pres[i.val]+300) :=
      Finset.sum_congr rfl (fun i _ => by rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.prefixAt_eq_get pres i.isLt])
    _ = _ := Fin.sum_univ_fun_getElem pres
      (fun pre => _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminal.time p shift left right NL NR q k pre+300)



variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem prefix_time_le {h J k NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (left right : ℕ→ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (pre : List (Finset (Fin (464*h)))) (hk : k≤J) (hp : _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix w.2.2 k pre)
    (hkey : w.1∈A ∧ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ (a w.1%(p : ℤ)+_root_.ThreeSum.RawIncidences.lift w.2.1*(p : ℤ)+shift)-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminal.time p shift left right NL NR w.2.2 k pre+300 ≤
      240*_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w k pre+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.charge h J k := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.time_le p shift A B C a b c left right eL eR hvL hvR w pre hk hp hkey
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminal.time _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalPrepared.time _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.charge
  omega



end ThreeSum.ReportingHostTerminalFrontier

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier

open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
open scoped _root_.BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
section

theorem ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.frontier_time_le__implementation_a186f47ce9 {h J k NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (left right : ℕ→ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (hk : k≤J)
    (hkey : w.1∈A ∧ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ (a w.1%(p : ℤ)+_root_.ThreeSum.RawIncidences.lift w.2.1*(p : ℤ)+shift)-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2) :
    let I := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
    let pres := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w k
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.time p shift left right NL NR w.2.2 k pres pres.length≤
      240*(_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.domain I w).card+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.charge h J k*pres.length+30 := by
  dsimp only
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.time_all]
  let I := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
  let pres := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w k
  have hsum : (pres.map (fun pre => _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminal.time p shift left right NL NR w.2.2 k pre+300)).sum≤
      (pres.map (fun pre => 240*_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery I w k pre+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.charge h J k)).sum := by
    apply List.sum_le_sum
    intro pre hpre
    exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.prefix_time_le p shift A B C a b c left right eL eR hvL hvR w pre hk
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.frontier_valid I w hk hpre) hkey
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalCosts.sum_linear,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalCosts.frontier_mass I w hk] at hsum
  dsimp only [pres,I] at hsum
  omega
end

end

theorem solution.{u_implementation_0,u_implementation_1,u_implementation_2} : type_of% (@ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.frontier_time_le__implementation_a186f47ce9.{u_implementation_0,u_implementation_1,u_implementation_2}) := (@ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.frontier_time_le__implementation_a186f47ce9.{u_implementation_0,u_implementation_1,u_implementation_2})

#print axioms solution
