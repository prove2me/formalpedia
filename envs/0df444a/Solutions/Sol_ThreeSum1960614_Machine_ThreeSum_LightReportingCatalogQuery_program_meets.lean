-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogQuery.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:35:51.19565+00:00
-- url     : https://prove2.me/submissions/d65c8180-cefd-4f89-8f05-9c8aa6b851e4

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

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
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingCatalogLookup_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingSuffixQueryIndexed_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_ReportingHostPrefixMasks_maskPair_injective
import Theorems.Thm_ThreeSum_RadixKeyLists_tuples_nodup
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_pairs_length
import Theorems.Thm_ThreeSum_SubsetAddress_enumerateLayer_nodup
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt

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
namespace ThreeSum.LayerCounts
end ThreeSum.LayerCounts
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingCatalogQuery
end ThreeSum.LightReportingCatalogQuery
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightSignedLeafBatch
end ThreeSum.LightSignedLeafBatch
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostCatalogSelection
end ThreeSum.ReportingHostCatalogSelection
namespace ThreeSum.ReportingHostPackedCatalog
end ThreeSum.ReportingHostPackedCatalog
namespace ThreeSum.ReportingHostPairEnumeration
end ThreeSum.ReportingHostPairEnumeration
namespace ThreeSum.ReportingHostPairSegments
end ThreeSum.ReportingHostPairSegments
namespace ThreeSum.ReportingHostPrefixCatalog
end ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum.ReportingHostPrefixMasks
end ThreeSum.ReportingHostPrefixMasks
namespace ThreeSum.ReportingHostPrefixOrder
end ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum.ReportingHostQueryBounds
end ThreeSum.ReportingHostQueryBounds
namespace ThreeSum.ReportingHostRelocation
end ThreeSum.ReportingHostRelocation
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
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
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LayerCounts
end ThreeSum1960614.Machine.ThreeSum.LayerCounts
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogQuery
end ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch
end ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaCell
end ThreeSum1960614.Machine.ThreeSum.LightZetaCell
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalGraph
end ThreeSum1960614.Machine.ThreeSum.LocalGraph
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.MaskDecode
end ThreeSum1960614.Machine.ThreeSum.MaskDecode
namespace ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
end ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogSelection
end ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogSelection
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPairSegments
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPairSegments
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostQueryBounds
end ThreeSum1960614.Machine.ThreeSum.ReportingHostQueryBounds
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
end ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

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









@[simp] theorem mem_join {J L : ℕ} {I : Finset (Fin J)}
    {u : Fin J → Finset (Fin L)} {i : Fin J} {x : Fin L} :
    Sigma.mk i x ∈ _root_.ThreeSum.BlockRows.join I u ↔ i ∈ I ∧ x ∈ u i := Finset.mem_sigma





































@[simp] theorem mem_prefixIndices {J k : ℕ} {i : Fin J} :
    i ∈ _root_.ThreeSum.BlockRows.prefixIndices J k ↔ i.val < k := by simp [_root_.ThreeSum.BlockRows.prefixIndices]



end ThreeSum.BlockRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Compact addresses for bounded-cardinality bit masks

Both ranking and enumeration recurse on the highest available bit. The
enumerator stops immediately when the requested layer is empty. In
particular, it does not enumerate the ambient Boolean cube and filter it.
-/

namespace ThreeSum.SubsetAddress
open _root_.ThreeSum.SubsetAddress


set_option maxRecDepth 4000

open _root_.Finset
open scoped _root_.BigOperators

















































theorem layerOffset_succ (L k : ℕ) :
    _root_.ThreeSum.SubsetAddress.layerOffset L (k + 1) = _root_.ThreeSum.SubsetAddress.layerOffset L k + L.choose k := by
  exact Finset.sum_range_succ _ _

theorem layerOffset_mono (L : ℕ) : Monotone (_root_.ThreeSum.SubsetAddress.layerOffset L) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ]
  omega





theorem downsetRank_lt {L cut m : ℕ} (hm : m < 2 ^ L) (hk : _root_.ThreeSum.SubsetAddress.weight L m ≤ cut) :
    _root_.ThreeSum.SubsetAddress.downsetRank L m < _root_.ThreeSum.SubsetAddress.downsetCap L cut := by
  have hmask : _root_.ThreeSum.SubsetAddress.IsMask L (_root_.ThreeSum.SubsetAddress.weight L m) m := ⟨hm, rfl⟩
  have hr := _root_.ThreeSum.SubsetAddress.layerRank_lt hmask
  unfold _root_.ThreeSum.SubsetAddress.downsetRank _root_.ThreeSum.SubsetAddress.downsetCap
  calc
    _ < _root_.ThreeSum.SubsetAddress.layerOffset L (_root_.ThreeSum.SubsetAddress.weight L m) + L.choose (_root_.ThreeSum.SubsetAddress.weight L m) := Nat.add_lt_add_left hr _
    _ = _root_.ThreeSum.SubsetAddress.layerOffset L (_root_.ThreeSum.SubsetAddress.weight L m + 1) := (_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ L _).symm
    _ ≤ _ := _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_mono L (Nat.succ_le_succ (le_min hk hmask.le_width))





















































theorem subsetRank_lt {L cut : ℕ} {s : Finset (Fin L)} (hs : s.card ≤ cut) :
    _root_.ThreeSum.SubsetAddress.subsetRank s < _root_.ThreeSum.SubsetAddress.downsetCap L cut := by
  have hm := _root_.ThreeSum.SubsetAddress.subsetMask_isMask s
  exact _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.downsetRank_lt hm.1 (hm.2.trans_le hs)











end ThreeSum.SubsetAddress

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Proof rules for the light language

Ends lim P d s σ T Q says: the statement s, started in σ, ends within T steps in a state that
satisfies Q.  There is one rule for each construct; a rule turns a goal about a statement into goals
about its parts, so a proof follows the text of the program from top to bottom.  Recursion needs no
rule: a statement about a recursive procedure is proved by induction (in Lean) on a measure, and the
rule for calls unfolds the body.

There are three rules for loops: with an invariant indexed by the number of the round and a cost for
each round (Ends.while), the same with one cost for all rounds (Ends.whileConst), and, for a loop
whose number of rounds depends on the data, with a quantity that every round decreases
(Ends.whileVariant).

The file also has the basic facts about runs (a run stays a run when procedures are appended to the
program), notation for writing programs, the simplification set
`light_norm`, and the standing assumptions `Std` about the limits.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Runs -/

/-- A procedure of a program is a procedure, with the same number, of the program with more
procedures appended. -/
theorem getElem?_append_of_eq_some {P : _root_.ThreeSum1960614.Machine.Light.Program} {p : ℕ} {body : _root_.ThreeSum1960614.Machine.Light.Stmt} (h : P[p]? = some body)
    (R : _root_.ThreeSum1960614.Machine.Light.Program) : (P ++ R)[p]? = some body := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h





/-- A run stays a run when procedures are appended to the program. -/
theorem Exec.append {s : _root_.ThreeSum1960614.Machine.Light.Stmt} {σ σ' : _root_.ThreeSum1960614.Machine.Light.State} {c : ℕ} (h : _root_.ThreeSum1960614.Machine.Light.Exec lim P d s σ σ' c) (R : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Exec lim (P ++ R) d s σ σ' c := by
  induction h with
  | skip => exact _root_.ThreeSum1960614.Machine.Light.Exec.skip
  | set h => exact _root_.ThreeSum1960614.Machine.Light.Exec.set h
  | store h₁ h₂ h₃ => exact _root_.ThreeSum1960614.Machine.Light.Exec.store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.call h₁ (_root_.ThreeSum1960614.Machine.Light.getElem?_append_of_eq_some h₂ R) h₃ ih

/-! ## The rules -/





/-- What is proved about a program holds for the program with more procedures appended. -/
theorem Ends.append {s σ T Q} (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d s σ T Q) (R : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim (P ++ R) d s σ T Q := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he.append R, hc, hq⟩























/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/


















/-! ## Simplification -/

attribute [simp] _root_.ThreeSum1960614.Machine.Light.Expr.val _root_.ThreeSum1960614.Machine.Light.Expr.cost _root_.ThreeSum1960614.Machine.Light.Expr.Safe _root_.Light.Op.eval _root_.ThreeSum1960614.Machine.Light.Cond.Holds _root_.ThreeSum1960614.Machine.Light.Cond.cost _root_.ThreeSum1960614.Machine.Light.Cond.Safe _root_.Light.frame





/-- The natural number behind an address that is a sum of two natural numbers. -/
@[simp] theorem toNat_natCast_add_natCast (a b : ℕ) : ((a : ℤ) + (b : ℤ)).toNat = a + b := by
  rw [← Nat.cast_add, Int.toNat_natCast]

/-! ## The limits -/









end Light

end

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









@[simp] theorem mem_indexSet {J L : ℕ} (S : Finset (_root_.ThreeSum.BlockRows.Coord J L)) (c : _root_.ThreeSum.BlockRows.Coord J L) :
    _root_.ThreeSum.BlockIndex.coordEquiv J L c ∈ _root_.ThreeSum.BlockIndex.indexSet S ↔ c ∈ S := by
  simp [_root_.ThreeSum.BlockIndex.indexSet]

























end ThreeSum.BlockIndex

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Calls

Meets lim P p d vals μ T R is the specification of a procedure: procedure number p of the program P,
run at depth d on the arguments vals in the memory μ, ends within T steps with a result and a memory
that satisfy R. A routine is proved to meet such a specification (Meets.of_body), and a caller uses
the specification only, so that the proof of a caller does not depend on the body of a callee.

The specification of a routine x, as its callers assume it, has the form
`∀ (data) μ, hypotheses → ∀ d, d + k ≤ lim.depth → Meets lim P p d vals μ T R`.  Here k is the
number of levels of calls that x needs below itself, and d, the depth at which the body of x runs,
comes last.

There is one rule for calls, in four forms.  It is told the fact about the callee, from which it
reads the values of the arguments, the time and what holds afterwards, and it asks for what follows
the call.  Three side goals have default proofs: the arguments are safe and have these values, one
more level of calls is allowed, and the time suffices.  Ends.callTo and Ends.callToThen are the rule
for a state ⟨frame l, μ⟩; Ends.callLast and Ends.callThen are the same for local variables that are
not given as a list.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Specifications of procedures -/



section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}

/-- From a theorem about a body to the specification. -/
theorem Meets.of_body {args : List ℤ} {Q : ℤ → (ℕ → ℤ) → Prop} {body : _root_.ThreeSum1960614.Machine.Light.Stmt}
    (hp : P[p]? = some body)
    (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d body ⟨_root_.Light.frame args, μ⟩ T fun σ' => Q (σ'.loc 0) σ'.mem) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d args μ T Q :=
  ⟨body, hp, h⟩







/-- A specification holds for the program with more procedures appended. -/
theorem Meets.append (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (P' : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim (P ++ P') p d vals μ T R := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, _root_.ThreeSum1960614.Machine.Light.getElem?_append_of_eq_some hp P', he.append P'⟩

end

/-! ## The rule for calls -/

section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List _root_.ThreeSum1960614.Machine.Light.Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} {s : _root_.ThreeSum1960614.Machine.Light.Stmt}









end

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Segments of the memory

Seg μ a l says that the cells a, a + 1, …, a + l.length - 1 of the memory μ hold the list l.
SegN is Seg for a list of natural numbers, MatAt for a matrix written row by row, VecAt for a vector
of indices.  The file has the lemmas for reading a cell of a segment, writing into it, writing
elsewhere, and for cutting and joining segments.  Each of the four predicates has its lemma `keep`,
which carries it to a later memory.
-/

@[expose] public section

namespace Light
open _root_.Light


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp





variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}





















































/-- Reading a cell of a segment of natural numbers, with the proof that the index is in range. -/
theorem SegN.getElem {l : List ℕ} (h : _root_.ThreeSum1960614.Machine.Light.SegN μ a l) {i : ℕ} (hi : i < l.length) :
    μ (a + i) = (l[i] : ℕ) := by
  rw [h i (by simpa using hi), List.getElem_map]

























end Light

end

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
# Exact relocation of closed verified procedure libraries

Every procedure call is shifted by the same list offset. The structural
execution proof preserves the exact initial/final states, runtime, memory
addresses, values, and depth budget. It permits composition of independently
verified fixed programs without assuming a new implementation contract.
-/

namespace ThreeSum.ReportingHostRelocation
open _root_.ThreeSum.ReportingHostRelocation


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light





theorem lookup {P : _root_.ThreeSum1960614.Machine.Light.Program} {p : ℕ} {body : _root_.ThreeSum1960614.Machine.Light.Stmt} (h : P[p]? = some body) (prefixProgram : _root_.ThreeSum1960614.Machine.Light.Program) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program prefixProgram P)[prefixProgram.length+p]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate prefixProgram.length body) := by
  apply _root_.ThreeSum1960614.Machine.Light.getElem?_append_length_add
  rw [List.getElem?_map,h]
  rfl

theorem exec {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {s : _root_.ThreeSum1960614.Machine.Light.Stmt} {σ σ' : _root_.ThreeSum1960614.Machine.Light.State} {c : ℕ}
    (h : _root_.ThreeSum1960614.Machine.Light.Exec lim P d s σ σ' c) (prefixProgram : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Exec lim (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program prefixProgram P) d (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate prefixProgram.length s) σ σ' c := by
  induction h with
  | skip => exact _root_.ThreeSum1960614.Machine.Light.Exec.skip
  | set h => exact _root_.ThreeSum1960614.Machine.Light.Exec.set h
  | store h₁ h₂ h₃ => exact _root_.ThreeSum1960614.Machine.Light.Exec.store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.call h₁ (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.lookup h₂ prefixProgram) h₃ ih

theorem ends {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {s : _root_.ThreeSum1960614.Machine.Light.Stmt} {σ : _root_.ThreeSum1960614.Machine.Light.State} {T : ℕ} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}
    (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d s σ T Q) (prefixProgram : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program prefixProgram P) d (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate prefixProgram.length s) σ T Q := by
  obtain ⟨σ',c,he,hc,hq⟩ := h
  exact ⟨σ',c,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.exec he prefixProgram,hc,hq⟩

theorem meets {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {p d : ℕ} {vals : List ℤ} {μ : ℕ → ℤ}
    {T : ℕ} {R : ℤ → (ℕ → ℤ) → Prop} (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (prefixProgram : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program prefixProgram P) (prefixProgram.length+p) d vals μ T R := by
  obtain ⟨body,hbody,he⟩ := h
  exact ⟨_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate prefixProgram.length body,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.lookup hbody prefixProgram,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.ends he prefixProgram⟩

end ThreeSum.ReportingHostRelocation

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Initial signed-product table writes on one actual mask layer -/

namespace ThreeSum.LightSignedLeafBatch
open _root_.ThreeSum.LightSignedLeafBatch


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightZetaCell
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell
open _root_.ThreeSum.MaskDecode
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskDecode

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem storedThrough_of_on {W cut base : ℕ} {μ μ' : ℕ → ℤ}
    {f : Finset (Fin W) → ℤ}
    (h : _root_.ThreeSum.LightZetaStages.StoredThrough μ base cut f W)
    (hkeep : ∀ i, base ≤ i → i < base+(W+1)*_root_.ThreeSum.SubsetAddress.downsetCap W cut → μ' i = μ i) :
    _root_.ThreeSum.LightZetaStages.StoredThrough μ' base cut f W := by
  intro j hj S hS
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.subsetRank_lt hS
  have hm := Nat.mul_le_mul_right (_root_.ThreeSum.SubsetAddress.downsetCap W cut) (Nat.succ_le_succ hj)
  simp only [Nat.succ_mul] at hm
  have he := hkeep (base+j*_root_.ThreeSum.SubsetAddress.downsetCap W cut+_root_.ThreeSum.SubsetAddress.subsetRank S) (by omega) (by
    simp only [Nat.succ_mul]
    omega)
  exact he.trans (h j hj S hS)















end ThreeSum.LightSignedLeafBatch

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact prefix catalog keys and sharing for fixed source occurrences

A catalog key consists only of the first k ordered disjoint balanced row
pairs. Its exact cardinality is (microOutputs*microPartitions)^k. Neither the
remaining output rows nor the wanted A-index enter a local box table once
the global occurrence vector is fixed.
-/

namespace ThreeSum.ReportingHostPrefixCatalog
open _root_.ThreeSum.ReportingHostPrefixCatalog


open _root_.Finset
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LayerCounts
open _root_.ThreeSum1960614.Machine.ThreeSum.LayerCounts
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix

set_option linter.unusedSectionVars false



















theorem leftSet_ofValidPrefix {h J k : ℕ} (hk : k ≤ J) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (pre : List (Finset (Fin (464*h)))) (hp : _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix q k pre) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.leftSet (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.ofValidPrefix hk q pre hp) = _root_.ThreeSum.BlockIndexedQuery.leftPrefix k (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre) := by
  ext x
  obtain ⟨⟨i,a⟩,rfl⟩ := (_root_.ThreeSum.BlockIndex.coordEquiv J (464*h)).surjective x
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.leftSet,_root_.ThreeSum.BlockIndexedQuery.leftPrefix,_root_.ThreeSum.BlockForced.prefixLeft,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.mem_indexSet,_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join,_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_prefixIndices]
  by_cases hi : i.val < k
  · simp only [hi,true_and,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.leftRows,dif_pos hi,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.ofValidPrefix]
  · simp only [hi,false_and]

theorem rightSet_ofValidPrefix {h J k : ℕ} (hk : k ≤ J) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (pre : List (Finset (Fin (464*h)))) (hp : _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix q k pre) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.rightSet (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.ofValidPrefix hk q pre hp) =
      _root_.ThreeSum.BlockIndexedQuery.rightPrefix k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre) := by
  ext x
  obtain ⟨⟨i,a⟩,rfl⟩ := (_root_.ThreeSum.BlockIndex.coordEquiv J (464*h)).surjective x
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.rightSet,_root_.ThreeSum.BlockIndexedQuery.leftPrefix,_root_.ThreeSum.BlockIndexedQuery.rightPrefix,_root_.ThreeSum.BlockForced.prefixLeft,_root_.ThreeSum.BlockForced.prefixRight,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.mem_indexSet,_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join,_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_prefixIndices]
  by_cases hi : i.val < k
  · simp only [hi,true_and,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.rightRows,dif_pos hi,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.ofValidPrefix]
  · simp only [hi,false_and]

section Sources

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]





theorem leftSource_eq {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource P B b q = _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.leftSourceOf (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) P B b := rfl

theorem rightSource_eq {h J : ℕ} (P shift : ℤ) (C : Finset γ) (c : γ → ℤ) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource P shift C c q = _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.rightSourceOf (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) P shift C c := rfl











end Sources

end ThreeSum.ReportingHostPrefixCatalog

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Output bounds and stored-table preservation for actual query batching -/

namespace ThreeSum.ReportingHostQueryBounds
open _root_.ThreeSum.ReportingHostQueryBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open scoped _root_.BigOperators







theorem boxStored_of_on {W cut base : ℕ} {μ μ' : ℕ → ℤ} {f : Finset (Fin W) → ℤ}
    (h : _root_.ThreeSum.LightBoxStages.StoredThrough μ base cut f W)
    (hkeep : ∀ i, base ≤ i → i < base+(W+1)*_root_.ThreeSum.SubsetAddress.downsetCap W cut → μ' i = μ i) :
    _root_.ThreeSum.LightBoxStages.StoredThrough μ' base cut f W := by
  intro j hj S hS
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.subsetRank_lt hS
  have hm := Nat.mul_le_mul_right (_root_.ThreeSum.SubsetAddress.downsetCap W cut) (Nat.succ_le_succ hj)
  simp only [Nat.succ_mul] at hm
  have he := hkeep (base+j*_root_.ThreeSum.SubsetAddress.downsetCap W cut+_root_.ThreeSum.SubsetAddress.subsetRank S) (by omega) (by
    simp only [Nat.succ_mul]
    omega)
  exact he.trans (h j hj S hS)

end ThreeSum.ReportingHostQueryBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A direct ordered enumeration of every local balanced row pair

First enumerate the h-subsets, then enumerate h-subsets of each complement.
The list contains every edge exactly once and has the exact local catalog
size, without scanning the ambient Boolean cube or all pairs of vertices.
-/

namespace ThreeSum.ReportingHostPairEnumeration
open _root_.ThreeSum.ReportingHostPairEnumeration


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LayerCounts
open _root_.ThreeSum1960614.Machine.ThreeSum.LayerCounts
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph

set_option linter.unusedSimpArgs false











theorem lefts_nodup (L h : ℕ) : (_root_.ThreeSum.ReportingHostPairEnumeration.lefts L h).Nodup := by
  apply (_root_.ThreeSum.SubsetAddress.enumerateLayer_nodup L h).map_on
  intro a ha b hb he
  have hA := (_root_.ThreeSum.SubsetAddress.mem_enumerateLayer L h a).mp ha
  have hB := (_root_.ThreeSum.SubsetAddress.mem_enumerateLayer L h b).mp hb
  simpa only [_root_.ThreeSum.MaskDecode.subsetMask_decode hA.1,_root_.ThreeSum.MaskDecode.subsetMask_decode hB.1] using
    congrArg _root_.ThreeSum.SubsetAddress.subsetMask he







theorem rights_nodup {L : ℕ} (S : Finset (Fin L)) (h : ℕ) : (_root_.ThreeSum.ReportingHostPairEnumeration.rights S h).Nodup :=
  _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.missingSets_nodup _ _



theorem pairs_nodup (L h : ℕ) : (_root_.ThreeSum.ReportingHostPairEnumeration.pairs L h).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro S _
    exact (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration.rights_nodup S h).map (fun a b he => congrArg Prod.snd he)
  · exact (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration.lefts_nodup L h).imp fun {S T} hST p hp hq => by
      obtain ⟨R,_,rfl⟩ := List.mem_map.mp hp
      obtain ⟨U,_,he⟩ := List.mem_map.mp hq
      exact hST (congrArg Prod.fst he).symm



















end ThreeSum.ReportingHostPairEnumeration

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Positional products are the physical masks of the complete shared prefix catalog

Both left and right products use one common tuple list. Every original valid
prefix has a key in that list, and the tuple encodes exactly its original
row-major global masks.
-/

namespace ThreeSum.ReportingHostPrefixMasks
open _root_.ThreeSum.ReportingHostPrefixMasks


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.BlockMaskLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
open _root_.ThreeSum.ReportingHostPairEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration
open scoped _root_.BigOperators

set_option maxHeartbeats 500000

variable {α : Type*}







theorem tuple_length {h k : ℕ} (p : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.Prefix h k) : (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.tuple p).length = k := by simp [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.tuple]









theorem tuple_mem {h k : ℕ} (p : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.Prefix h k) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.tuple p ∈ _root_.ThreeSum.RadixKeyLists.tuples (_root_.ThreeSum.ReportingHostPairEnumeration.pairs (464*h) h) k := by
  apply (_root_.ThreeSum.RadixKeyLists.mem_tuples _ _ _).mpr
  refine ⟨_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.tuple_length p,?_⟩
  intro q hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  exact (_root_.ThreeSum.ReportingHostPairEnumeration.pairs_mem _).mpr (p i).property

theorem tuple_injective {h k : ℕ} : Function.Injective (@_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.tuple h k) := by
  intro p q he
  funext i
  apply Subtype.ext
  have hh := congrArg (fun xs => xs[i.val]?) he
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.tuple,List.getElem?_ofFn,dif_pos i.isLt,Option.some.injEq] using hh



theorem tuple_ofTuple {h k : ℕ} (xs : List (Finset (Fin (464*h)) × Finset (Fin (464*h))))
    (hlen : xs.length = k) (hmem : ∀ q ∈ xs, q ∈ _root_.ThreeSum.ReportingHostPairEnumeration.pairs (464*h) h) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.tuple (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.ofTuple xs hlen hmem) = xs := by
  apply List.ext_getElem
  · simp [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.tuple,hlen]
  · intro i hi hi'
    simp [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.tuple,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.ofTuple]





end ThreeSum.ReportingHostPrefixMasks

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Complete shared prefix records in the physical product-constructor order

The semantic list is obtained from the actual tuple list, without filtering,
reordering, or coalescing equal left/right projections. It connects both
constructed integer arrays to every exact global prefix-mask pair.
-/

namespace ThreeSum.ReportingHostPrefixOrder
open _root_.ThreeSum.ReportingHostPrefixOrder


open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
open _root_.ThreeSum.ReportingHostPairEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks
open _root_.ThreeSum.ReportingHostPairSegments
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairSegments

set_option maxHeartbeats 600000



theorem prefixes_length (h k : ℕ) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes h k).length = ((464*h).choose (2*h)*(2*h).choose h)^k := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes,List.length_map,List.length_attach,_root_.ThreeSum.RadixKeyLists.tuples_length,_root_.ThreeSum.ReportingHostPairEnumeration.pairs_length]

theorem prefixes_tuple (h k : ℕ) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes h k).map _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.tuple = _root_.ThreeSum.RadixKeyLists.tuples (_root_.ThreeSum.ReportingHostPairEnumeration.pairs (464*h) h) k := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes
  simp only [List.map_map,Function.comp_def,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.tuple_ofTuple]
  simp

theorem mem_prefixes {h k : ℕ} (p : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.Prefix h k) : p ∈ _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes h k := by
  have hm : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.tuple p ∈ (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes h k).map _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.tuple := by
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes_tuple]
    exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.tuple_mem p
  obtain ⟨q,hq,he⟩ := List.mem_map.mp hm
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.tuple_injective he) ▸ hq

theorem prefixes_nodup (h k : ℕ) : (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes h k).Nodup := by
  apply List.Nodup.of_map
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes_tuple]
  exact _root_.ThreeSum.RadixKeyLists.tuples_nodup _ (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration.pairs_nodup _ _) _












theorem preL_get {h J k i : ℕ} (hi : i < (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes h k).length) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL h J k i = _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.leftSet (J := J) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes h k)[i] := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.leftSets,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some,
    Option.getD_some]

theorem preR_get {h J k i : ℕ} (hi : i < (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes h k).length) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR h J k i = _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.rightSet (J := J) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes h k)[i] := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.rightSets,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some,
    Option.getD_some]





theorem exists_index {h J k : ℕ} (p : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.Prefix h k) :
    ∃ i < (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes h k).length, _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL h J k i = _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.leftSet (J := J) p ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR h J k i = _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.rightSet (J := J) p := by
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.mem_prefixes p)
  exact ⟨i,hi,by rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL_get hi,he],by rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR_get hi,he]⟩

theorem maskPair_unique {h J k i j : ℕ} (hk : k ≤ J)
    (hi : i < (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes h k).length) (hj : j < (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes h k).length)
    (hL : _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL h J k i) = _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL h J k j))
    (hR : _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR h J k i) = _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR h J k j)) : i=j := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL_get hi,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL_get hj] at hL
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR_get hi,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR_get hj] at hR
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.maskPair_injective hk (Prod.ext hL hR)
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes_nodup h k).getElem_inj_iff.mp he

end ThreeSum.ReportingHostPrefixOrder

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual complete shared prefix catalog from the original source tables

A single closed program constructs every aligned prefix-mask pair, reads its
computed count header, and builds all local suffix box tables. The original
record order is exact; no supplied enumeration, count, or table pointer is
used as an algorithmic oracle.
-/

namespace ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingPrefixCatalog


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}









theorem count_eq_length (h k : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k = (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes h k).length :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes_length h k).symm









end ThreeSum.LightReportingPrefixCatalog

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact sorted lookup of a prefix catalog record

Each original catalog position is retained as the low digit of a packed
integer. A sorted search uses the upper end of the requested key's interval;
the unique prefix-key proof forces that hit to be the original record, and
remainder recovers its unchanged catalog index.
-/

namespace ThreeSum.ReportingHostPackedCatalog
open _root_.ThreeSum.ReportingHostPackedCatalog


open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder

set_option maxHeartbeats 600000











theorem pairKey_injective {radix l r l' r' : ℕ} (hl : l < radix) (hl' : l' < radix)
    (he : _root_.ThreeSum.ReportingHostPackedCatalog.pairKey radix l r = _root_.ThreeSum.ReportingHostPackedCatalog.pairKey radix l' r') : l=l' ∧ r=r' := by
  have hm := congrArg (fun x => x%radix) he
  have hlr : l=l' := by simpa [_root_.ThreeSum.ReportingHostPackedCatalog.pairKey,Nat.add_mod,Nat.mod_eq_of_lt hl,Nat.mod_eq_of_lt hl'] using hm
  refine ⟨hlr,?_⟩
  unfold _root_.ThreeSum.ReportingHostPackedCatalog.pairKey at he
  rw [hlr] at he
  nlinarith

















theorem prefixKey_unique {h J k : ℕ} (hk : k ≤ J) :
    ∀ i < _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k,
    ∀ j < _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k,
      _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog.prefixKey h J k i=_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog.prefixKey h J k j → i=j := by
  intro i hi j hj he
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog.pairKey_injective (_root_.ThreeSum.SubsetAddress.subsetMask_isMask (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL h J k i)).1
    (_root_.ThreeSum.SubsetAddress.subsetMask_isMask (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL h J k j)).1 he
  exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.maskPair_unique hk (by rwa [← _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count_eq_length])
    (by rwa [← _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count_eq_length]) hp.1 hp.2

theorem prefix_count_le_pow {h J k : ℕ} (hk : k ≤ J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤ 2^(2*(J*(464*h))) := by
  have hhalf : 2*h ≤ 464*h := by omega
  have he : _root_.ThreeSum.LightReportingPrefixArrays.localCount (464*h) h ≤ 2^(2*(464*h)) := by
    calc
      _ ≤ 2^(464*h)*2^(2*h) := Nat.mul_le_mul (Nat.choose_le_two_pow _ _) (Nat.choose_le_two_pow _ _)
      _ ≤ 2^(464*h)*2^(464*h) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hhalf)
      _ = 2^(2*(464*h)) := by rw [← pow_add]; congr 1; omega
  calc
    _ ≤ (2^(2*(464*h)))^k := Nat.pow_le_pow_left he k
    _ = 2^(2*(k*(464*h))) := by rw [← pow_mul]; congr 1; ring
    _ ≤ 2^(2*(J*(464*h))) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hk))

end ThreeSum.ReportingHostPackedCatalog

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact original valid-prefix selection from the complete physical catalog

The index is a proof witness for the actual unique stored mask pair. It is not
an argument supplied to the querying machine: the physical sorted lookup
recovers it from the two original prefix masks.
-/

namespace ThreeSum.ReportingHostCatalogSelection
open _root_.ThreeSum.ReportingHostCatalogSelection


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
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
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog

theorem original_index {h J k : ℕ} (hk : k ≤ J) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (pre : List (Finset (Fin (464*h)))) (hp : _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix q k pre) :
    ∃ i < _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k,
      _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL h J k i = _root_.ThreeSum.BlockIndexedQuery.leftPrefix k (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre) ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR h J k i = _root_.ThreeSum.BlockIndexedQuery.rightPrefix k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre) := by
  obtain ⟨i,hi,hL,hR⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.exists_index (J := J) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.ofValidPrefix hk q pre hp)
  exact ⟨i,by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count_eq_length] using hi,
    hL.trans (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.leftSet_ofValidPrefix hk q pre hp),
    hR.trans (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.rightSet_ofValidPrefix hk q pre hp)⟩

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

theorem selected_leaf {h J k i : ℕ} (hk : k ≤ J)
    (P shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (pre : List (Finset (Fin (464*h)))) (ho : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q = o)
    (hL : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL h J k i = _root_.ThreeSum.BlockIndexedQuery.leftPrefix k (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre))
    (hR : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR h J k i = _root_.ThreeSum.BlockIndexedQuery.rightPrefix k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre)) :
    _root_.ThreeSum.ReportingHostSuffix.leafWeight (_root_.ThreeSum.ReportingHostSuffix.block_fit hk) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.leftSourceOf o P B b) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.rightSourceOf o P shift C c)
      (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL h J k i) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR h J k i) =
      _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixBoxes.localLeaf hk P shift B C b c q pre := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixBoxes.localLeaf
  rw [hL,hR,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.leftSource_eq,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.rightSource_eq,ho]
  rfl

theorem selected_box {μ : ℕ → ℤ} {h J k i boxCut boxBase : ℕ} (hk : k ≤ J)
    (P shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (pre : List (Finset (Fin (464*h)))) (ho : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q = o)
    (hi : i < _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k)
    (hL : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL h J k i = _root_.ThreeSum.BlockIndexedQuery.leftPrefix k (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre))
    (hR : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR h J k i = _root_.ThreeSum.BlockIndexedQuery.rightPrefix k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre))
    (hboxes : ∀ j < _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k, _root_.ThreeSum.LightBoxStages.StoredThrough μ
      (boxBase+j*_root_.ThreeSum.LightReportingSuffixCatalog.stride (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) boxCut) boxCut
      (_root_.ThreeSum.ReportingHostSuffix.leafWeight (_root_.ThreeSum.ReportingHostSuffix.block_fit hk) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.leftSourceOf o P B b) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.rightSourceOf o P shift C c)
        (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL h J k j) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR h J k j))
      (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k)) :
    _root_.ThreeSum.LightBoxStages.StoredThrough μ (boxBase+i*_root_.ThreeSum.LightReportingSuffixCatalog.stride (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) boxCut)
      boxCut (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixBoxes.localLeaf hk P shift B C b c q pre)
      (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) := by
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogSelection.selected_leaf hk P shift B C b c o q pre ho hL hR]
  exact hboxes i hi

theorem selected_box_end {N i boxBase boxCut V upper : ℕ} (hi : i < N)
    (hboxes : boxBase+N*_root_.ThreeSum.LightReportingSuffixCatalog.stride V boxCut ≤ upper) :
    boxBase+i*_root_.ThreeSum.LightReportingSuffixCatalog.stride V boxCut+(V+1)*_root_.ThreeSum.SubsetAddress.downsetCap V boxCut ≤ upper := by
  have hm := Nat.mul_le_mul_right (_root_.ThreeSum.LightReportingSuffixCatalog.stride V boxCut) (show i+1 ≤ N by omega)
  have hm' : i*_root_.ThreeSum.LightReportingSuffixCatalog.stride V boxCut+_root_.ThreeSum.LightReportingSuffixCatalog.stride V boxCut ≤ N*_root_.ThreeSum.LightReportingSuffixCatalog.stride V boxCut := by
    simpa only [Nat.add_mul,Nat.one_mul] using hm
  change boxBase+i*_root_.ThreeSum.LightReportingSuffixCatalog.stride V boxCut+_root_.ThreeSum.LightReportingSuffixCatalog.stride V boxCut ≤ upper
  omega

end ThreeSum.ReportingHostCatalogSelection

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogQuery

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
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
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogSelection
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogQuery.program_meets__implementation_411bc3d36b
    {μ : ℕ → ℤ} {h J k t baseL baseR boxCut boxBase indexBase ptrBase maskBase work depth : ℕ}
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)
    (pre : List (Finset (Fin (464*h)))) (hk : k ≤ J) (hp : _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix w.2.2 k pre)
    (hkey : w.1 ∈ A ∧ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣
      (a w.1 % pMod+_root_.ThreeSum.RawIncidences.lift w.2.1*pMod+shift)-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdataL : baseL+(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)*_root_.ThreeSum.SubsetAddress.downsetCap (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (_root_.ThreeSum.LightBlockQuery.sourceCut h J) ≤ maskBase)
    (hdataR : baseR+(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)*_root_.ThreeSum.SubsetAddress.downsetCap (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (_root_.ThreeSum.LightBlockQuery.sourceCut h J) ≤ maskBase)
    (hindex : indexBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤ maskBase) (hptr : ptrBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤ maskBase)
    (hboxesEnd : boxBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k*_root_.ThreeSum.LightReportingSuffixCatalog.stride (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) boxCut ≤ maskBase)
    (hmasks : maskBase+_root_.ThreeSum.LightSparseQuery.queryItems (_root_.ThreeSum.LightBlockQuery.residualSize h J k) t ≤ work)
    (hspace : work+1+_root_.ThreeSum.LightPascal.tableSize (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J)+(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1) ≤ lim.space)
    (hpowSpace : work+(2*_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+2) ≤ lim.space)
    (hemodSpace : work+(Nat.log 2 (_root_.ThreeSum.LightReportingCatalogLookup.valueBound (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k)+1)+2) ≤ lim.space)
    (hword : (((_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)*2^(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1) : ℕ) : ℤ) ≤ lim.word)
    (hlookupWord : (_root_.ThreeSum.LightReportingCatalogLookup.word (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k) : ℤ) ≤ lim.word)
    (hvalueWord : (_root_.ThreeSum.LightSparseQuery.magnitudeBound (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k)
      (_root_.ThreeSum.LightBlockQuery.residualSize h J k) t B.card C.card : ℤ) ≤ lim.word)
    (ht : t ≤ _root_.ThreeSum.LightBlockQuery.residualSize h J k+1) (hboxCut : boxCut ≤ _root_.ThreeSum.LightBlockQuery.residualSize h J k)
    (hflags : _root_.ThreeSum.LightBlockQuery.residualSize h J k-t ≤ boxCut)
    (hstoredL : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseL (_root_.ThreeSum.LightBlockQuery.sourceCut h J)
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource pMod B b w.2.2) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J))
    (hstoredR : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseR (_root_.ThreeSum.LightBlockQuery.sourceCut h J)
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource pMod shift C c w.2.2) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J))
    (hindexData : ∃ S : List ℤ, _root_.ThreeSum1960614.Machine.Light.Seg μ indexBase S ∧
      S.Perm (_root_.ThreeSum.ReportingHostPackedCatalog.codes (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog.prefixKey h J k) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k)) ∧
      S.Pairwise (· ≤ ·))
    (hptrs : _root_.ThreeSum1960614.Machine.Light.SegN μ ptrBase (List.ofFn fun i : Fin (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k) =>
      boxBase+i.val*_root_.ThreeSum.LightReportingSuffixCatalog.stride (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) boxCut))
    (hboxes : ∀ i < _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k, _root_.ThreeSum.LightBoxStages.StoredThrough μ
      (boxBase+i*_root_.ThreeSum.LightReportingSuffixCatalog.stride (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) boxCut) boxCut
      (_root_.ThreeSum.ReportingHostSuffix.leafWeight (_root_.ThreeSum.ReportingHostSuffix.block_fit hk) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource pMod B b w.2.2) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource pMod shift C c w.2.2)
        (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL h J k i) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR h J k i))
      (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k))
    (hd : depth+2*_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+12 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogQuery.program 35 depth
      [_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J,_root_.ThreeSum.LightBlockQuery.sourceCut h J,_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k,k*h,
        _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.leftPrefix k (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre)),k*h,
        _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.rightPrefix k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre)),
        _root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k,k*(464*h),_root_.ThreeSum.LightBlockQuery.residualSize h J k,_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.querySet k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2)),
        t,baseL,baseR,boxCut,indexBase,ptrBase,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k,maskBase,work]
      μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogQuery.time h J k t)
      (fun r μ' =>
        r = (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k pre : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' work maskBase (_root_.ThreeSum.LightSparseQuery.queryItems (_root_.ThreeSum.LightBlockQuery.residualSize h J k) t)) := by
  obtain ⟨i,hi,hL,hR⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogSelection.original_index hk w.2.2 pre hp
  obtain ⟨S,hseg,hperm,hsorted⟩ := hindexData
  have hEnd := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogSelection.selected_box_end hi hboxesEnd
  have hstoredBox := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogSelection.selected_box hk pMod shift B C b c (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences w.2.2) w.2.2 pre
    rfl hi hL hR hboxes
  have hreadPtr : μ (ptrBase+i) = (boxBase+i*_root_.ThreeSum.LightReportingSuffixCatalog.stride (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) boxCut : ℕ) := by
    have hp := hptrs.getElem (i := i) (by simpa only [List.length_ofFn] using hi)
    simpa only [List.getElem_ofFn,Nat.cast_add,Nat.cast_mul] using hp
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 35) (by rfl : program[35]? = some (body 3 34))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogQuery.body _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogQuery.time
  have hl := ((_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLookup.program_meets (d := depth+1) (μ := μ)
    (fun j => _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL h J k j)) (fun j => _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR h J k j)) hi
    hw (hindex.trans (by omega)) hpowSpace hemodSpace hlookupWord
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog.prefix_count_le_pow hk)
    (fun j _ => (_root_.ThreeSum.SubsetAddress.subsetMask_isMask (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL h J k j)).1)
    (fun j _ => (_root_.ThreeSum.SubsetAddress.subsetMask_isMask (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR h J k j)).1)
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog.prefixKey_unique hk) hperm hsorted hseg (by omega)).append
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQueryHost.program.map
        (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLookup.program.length))).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogQuery.body 3 34]
  rw [hL,hR] at hl
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     first
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hl _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hl ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingCatalogLookup.time, _root_.ThreeSum.LightReportingSuffixQueryHost.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightReportingCatalogLookup.time, _root_.ThreeSum.LightReportingSuffixQueryHost.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightReportingCatalogLookup.time, _root_.ThreeSum.LightReportingSuffixQueryHost.time] <;> omega)
     on_goal -1 => (rintro index μ₁ ⟨hfound, hkeepLookup⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hread : μ₁ (ptrBase+i) = (boxBase+i*_root_.ThreeSum.LightReportingSuffixCatalog.stride (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) boxCut : ℕ) :=
    (hkeepLookup _ (by omega)).trans hreadPtr
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (boxBase + i * _root_.ThreeSum.LightReportingSuffixCatalog.stride (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464 * h) k) boxCut : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hfound, hread, _root_.ThreeSum.LightReportingCatalogLookup.time, _root_.ThreeSum.LightReportingSuffixQueryHost.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hfound, hread, _root_.ThreeSum.LightReportingCatalogLookup.time, _root_.ThreeSum.LightReportingSuffixQueryHost.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hfound, hread, _root_.ThreeSum.LightReportingCatalogLookup.time, _root_.ThreeSum.LightReportingSuffixQueryHost.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hsourceL := _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch.storedThrough_of_on hstoredL
    (by intro j _ hj; exact hkeepLookup j ((hj.trans_le hdataL).trans_le (by omega)))
  have hsourceR := _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch.storedThrough_of_on hstoredR
    (by intro j _ hj; exact hkeepLookup j ((hj.trans_le hdataR).trans_le (by omega)))
  have hlocalBox := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostQueryBounds.boxStored_of_on hstoredBox
    (by intro j _ hj; exact hkeepLookup j (by omega))
  have hq := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.meets
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQueryIndexed.program_meets (depth := depth+1) (μ := μ₁)
      pMod shift A B C a b c w pre hk hp hkey hw hdataL hdataR hEnd hmasks hspace
      hword hvalueWord ht hboxCut hflags hsourceL hsourceR hlocalBox (by omega))
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLookup.program).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogQuery.body 3 34]
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     first
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hq _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hq ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingCatalogLookup.time, _root_.ThreeSum.LightReportingSuffixQueryHost.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightReportingCatalogLookup.time, _root_.ThreeSum.LightReportingSuffixQueryHost.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightReportingCatalogLookup.time, _root_.ThreeSum.LightReportingSuffixQueryHost.time] <;> omega)
     on_goal -1 => (rintro result μ₂ ⟨hresult, hkeepQuery⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  refine ⟨hresult,?_⟩
  intro j hj
  exact (hkeepQuery j hj).trans (hkeepLookup j hj.1)
end

end

theorem solution.{u_implementation_0,u_implementation_1,u_implementation_2} : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogQuery.program_meets__implementation_411bc3d36b.{u_implementation_0,u_implementation_1,u_implementation_2}) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogQuery.program_meets__implementation_411bc3d36b.{u_implementation_0,u_implementation_1,u_implementation_2})

#print axioms solution
