-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T08:57:50.544475+00:00
-- url     : https://prove2.me/submissions/4be526d3-a148-47c3-9c11-5a24e429e4f7

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingPrefixArrays_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingSuffixCatalogSetup_program_meets
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_pairs_length
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
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
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
namespace ThreeSum.MaskDifference
end ThreeSum.MaskDifference
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
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
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
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
namespace ThreeSum1960614.Machine.ThreeSum.MaskDifference
end ThreeSum1960614.Machine.ThreeSum.MaskDifference
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
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
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
end ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
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



@[simp] theorem coordEquiv_val {J L : ℕ} (i : Fin J) (x : Fin L) :
    (_root_.ThreeSum.BlockIndex.coordEquiv J L ⟨i,x⟩).val = i.val*L+x.val := by
  simp [_root_.ThreeSum.BlockIndex.coordEquiv, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]







@[simp] theorem indexSet_card {J L : ℕ} (S : Finset (_root_.ThreeSum.BlockRows.Coord J L)) :
    (_root_.ThreeSum.BlockIndex.indexSet S).card = S.card := Finset.card_map _























end ThreeSum.BlockIndex

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact arithmetic subtraction of one subset mask from another -/

namespace ThreeSum.MaskDifference
open _root_.ThreeSum.MaskDifference


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress

theorem subsetMask_sum {L : ℕ} (S : Finset (Fin L)) :
    _root_.ThreeSum.SubsetAddress.subsetMask S = ∑ i ∈ S, 2^i.val := by
  simp [_root_.ThreeSum.SubsetAddress.subsetMask,_root_.ThreeSum.SubsetAddress.maskOf,_root_.ThreeSum.SubsetAddress.natPositions]











end ThreeSum.MaskDifference

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



















theorem leftPrefix_card {J L h k : ℕ} (hk : k ≤ J) (u : Fin J → Finset (Fin L))
    (hu : ∀ i ∈ _root_.ThreeSum.BlockRows.prefixIndices J k, (u i).card = h) : (_root_.ThreeSum.BlockIndexedQuery.leftPrefix k u).card = k*h := by
  rw [_root_.ThreeSum.BlockIndexedQuery.leftPrefix,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.indexSet_card,_root_.ThreeSum.BlockForced.prefixLeft,_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_card_of_balance _ _ hu,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.prefixIndices_card hk]











section Histograms

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]



















end Histograms

end ThreeSum.BlockIndexedQuery

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

/-! # Exact row-major mask packing and prefix scan invariants -/

namespace ThreeSum.BlockMaskLayout
open _root_.ThreeSum.BlockMaskLayout


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open scoped _root_.BigOperators





theorem mask_join {J L : ℕ} (I : Finset (Fin J)) (rows : Fin J → Finset (Fin L)) :
    _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndex.indexSet (_root_.ThreeSum.BlockRows.join I rows)) = ∑ i ∈ I, _root_.ThreeSum.BlockMaskLayout.rowMask rows i := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.MaskDifference.subsetMask_sum]
  unfold _root_.ThreeSum.BlockIndex.indexSet
  rw [Finset.sum_map]
  unfold _root_.ThreeSum.BlockRows.join
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Equiv.toEmbedding_apply,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.coordEquiv_val,pow_add,_root_.ThreeSum.BlockMaskLayout.rowMask,
    _root_.ThreeSum1960614.Machine.ThreeSum.MaskDifference.subsetMask_sum,Finset.mul_sum]

























end ThreeSum.BlockMaskLayout

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













theorem leftSet_card {h J k : ℕ} (hk : k ≤ J) (p : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.Prefix h k) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.leftSet (J := J) p).card = k*h := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftPrefix_card hk
  intro i hi
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.leftRows,dif_pos (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_prefixIndices.mp hi)]
  exact (_root_.ThreeSum.LocalGraph.edge_data _).1

theorem rightSet_card {h J k : ℕ} (hk : k ≤ J) (p : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.Prefix h k) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.rightSet (J := J) p).card = k*h := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftPrefix_card hk
  intro i hi
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.rightRows,dif_pos (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_prefixIndices.mp hi)]
  exact (_root_.ThreeSum.LocalGraph.edge_data _).2.1







section Sources

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]



















end Sources

end ThreeSum.ReportingHostPrefixCatalog

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

theorem positionalHash_ofFn (p : ℤ) (raw : α → ℤ) {k : ℕ} (f : Fin k → α) :
    _root_.ThreeSum.Radix.positionalHash p raw (List.ofFn f) = ∑ i : Fin k, p^i.val*raw (f i) := by
  induction k with
  | zero => simp [_root_.ThreeSum.Radix.positionalHash]
  | succ k ih =>
    rw [List.ofFn_succ,_root_.ThreeSum.Radix.positionalHash,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,pow_zero,one_mul,Fin.val_succ,pow_succ]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring

theorem mask_rows_ofFin {J L k : ℕ} (hk : k ≤ J) (u : Fin k → Finset (Fin L)) :
    _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.leftPrefix k (fun i : Fin J => if hi : i.val < k then u ⟨i.val,hi⟩ else ∅)) =
      ∑ i : Fin k, 2^(i.val*L)*_root_.ThreeSum.SubsetAddress.subsetMask (u i) := by
  rw [_root_.ThreeSum.BlockIndexedQuery.leftPrefix,_root_.ThreeSum.BlockForced.prefixLeft,_root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout.mask_join]
  refine Finset.sum_bij (fun i hi => (⟨i.val,_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_prefixIndices.mp hi⟩ : Fin k)) ?_ ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_univ _
  · intro i hi j hj he
    exact Fin.ext (congrArg (fun a : Fin k => a.val) he)
  · intro i hi
    exact ⟨⟨i.val,i.isLt.trans_le hk⟩,_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_prefixIndices.mpr i.isLt,rfl⟩
  · intro i hi
    simp only [_root_.ThreeSum.BlockMaskLayout.rowMask,dif_pos (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_prefixIndices.mp hi)]





theorem leftSet_mask {h J k : ℕ} (hk : k ≤ J) (p : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.Prefix h k) :
    _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.leftSet (J := J) p) = ∑ i : Fin k, 2^(i.val*(464*h))*_root_.ThreeSum.SubsetAddress.subsetMask (p i).val.1 := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.leftSet _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.leftRows
  exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.mask_rows_ofFin (J := J) (L := 464*h) (k := k) hk (fun i => (p i).val.1)

theorem rightSet_mask {h J k : ℕ} (hk : k ≤ J) (p : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.Prefix h k) :
    _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.rightSet (J := J) p) = ∑ i : Fin k, 2^(i.val*(464*h))*_root_.ThreeSum.SubsetAddress.subsetMask (p i).val.2 := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.rightSet _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.rightRows
  exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.mask_rows_ofFin (J := J) (L := 464*h) (k := k) hk (fun i => (p i).val.2)

theorem leftHash_eq_mask {h J k : ℕ} (hk : k ≤ J) (p : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.Prefix h k) :
    _root_.ThreeSum.Radix.positionalHash ((2^(464*h) : ℕ) : ℤ) (fun q => (_root_.ThreeSum.SubsetAddress.subsetMask q.1 : ℤ)) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.tuple p) =
      (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.leftSet (J := J) p) : ℤ) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.tuple,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.positionalHash_ofFn,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.leftSet_mask hk]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  simp only [← pow_mul,Nat.mul_comm]

theorem rightHash_eq_mask {h J k : ℕ} (hk : k ≤ J) (p : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.Prefix h k) :
    _root_.ThreeSum.Radix.positionalHash ((2^(464*h) : ℕ) : ℤ) (fun q => (_root_.ThreeSum.SubsetAddress.subsetMask q.2 : ℤ)) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.tuple p) =
      (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.rightSet (J := J) p) : ℤ) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.tuple,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.positionalHash_ofFn,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.rightSet_mask hk]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  simp only [← pow_mul,Nat.mul_comm]







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












theorem left_values {h J k : ℕ} (hk : k ≤ J) :
    _root_.ThreeSum.RadixKeyLists.values ((2^(464*h) : ℕ) : ℤ) (_root_.ThreeSum.ReportingHostPairSegments.leftMasks (464*h) h) k =
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.leftSets h J k).map (fun S => (_root_.ThreeSum.SubsetAddress.subsetMask S : ℤ)) := by
  rw [_root_.ThreeSum.ReportingHostPairSegments.leftMasks,_root_.ThreeSum.RadixKeyLists.values_eq_map,← _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes_tuple]
  simp only [List.map_map,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.leftSets,Function.comp_def,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.leftHash_eq_mask hk]

theorem right_values {h J k : ℕ} (hk : k ≤ J) :
    _root_.ThreeSum.RadixKeyLists.values ((2^(464*h) : ℕ) : ℤ) (_root_.ThreeSum.ReportingHostPairSegments.rightMasks (464*h) h) k =
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.rightSets h J k).map (fun S => (_root_.ThreeSum.SubsetAddress.subsetMask S : ℤ)) := by
  rw [_root_.ThreeSum.ReportingHostPairSegments.rightMasks,_root_.ThreeSum.RadixKeyLists.values_eq_map,← _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes_tuple]
  simp only [List.map_map,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.rightSets,Function.comp_def,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixMasks.rightHash_eq_mask hk]

theorem preL_get {h J k i : ℕ} (hi : i < (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes h k).length) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL h J k i = _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.leftSet (J := J) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes h k)[i] := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.leftSets,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some,
    Option.getD_some]

theorem preR_get {h J k i : ℕ} (hi : i < (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes h k).length) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR h J k i = _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.rightSet (J := J) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes h k)[i] := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.rightSets,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some,
    Option.getD_some]

theorem preL_card {h J k i : ℕ} (hk : k ≤ J) (hi : i < (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes h k).length) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL h J k i).card = k*h := by rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL_get hi]; exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.leftSet_card hk _

theorem preR_card {h J k i : ℕ} (hk : k ≤ J) (hi : i < (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes h k).length) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR h J k i).card = k*h := by rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR_get hi]; exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.rightSet_card hk _





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

theorem count_pos (h k : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k := by
  exact Nat.pow_pos (Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega)))

theorem readL {h J k a : ℕ} {μ : ℕ → ℤ} (hk : k ≤ J)
    (hs : _root_.ThreeSum1960614.Machine.Light.Seg μ a (_root_.ThreeSum.RadixKeyLists.values ((2^(464*h) : ℕ) : ℤ)
      (_root_.ThreeSum.ReportingHostPairSegments.leftMasks (464*h) h) k)) :
    ∀ i < _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k, μ (a+i) = (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL h J k i) : ℤ) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.left_values hk] at hs
  intro i hi
  have hi' : i < (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes h k).length := by rwa [← _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count_eq_length]
  have hh := hs i (by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.leftSets,List.length_map] using hi')
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.leftSets,List.getElem_map,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL_get hi'] using hh

theorem readR {h J k a : ℕ} {μ : ℕ → ℤ} (hk : k ≤ J)
    (hs : _root_.ThreeSum1960614.Machine.Light.Seg μ a (_root_.ThreeSum.RadixKeyLists.values ((2^(464*h) : ℕ) : ℤ)
      (_root_.ThreeSum.ReportingHostPairSegments.rightMasks (464*h) h) k)) :
    ∀ i < _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k, μ (a+i) = (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR h J k i) : ℤ) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.right_values hk] at hs
  intro i hi
  have hi' : i < (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.prefixes h k).length := by rwa [← _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count_eq_length]
  have hh := hs i (by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.rightSets,List.length_map] using hi')
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.rightSets,List.getElem_map,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR_get hi'] using hh



end ThreeSum.LightReportingPrefixCatalog

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog

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
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.program_meets__implementation_4679c03db3 {μ : ℕ → ℤ}
    {h J k cut boxCut baseL baseR srcS pairL pairR stageL stageR ptrBase boxBase maskBase work B D d : ℕ}
    (hk : k ≤ J) (f g : Finset (Fin (J*(464*h))) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hcut : cut ≤ J*(464*h)) (hboxCut : boxCut ≤ (J-k)*(464*h))
    (hdataL : baseL+(J*(464*h)+1)*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤ srcS)
    (hdataR : baseR+(J*(464*h)+1)*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤ srcS)
    (hS : srcS+(464*h).choose h ≤ pairL)
    (hL : pairL+_root_.ThreeSum.LightReportingPrefixArrays.localCount (464*h) h ≤ pairR)
    (hR : pairR+_root_.ThreeSum.LightReportingPrefixArrays.localCount (464*h) h ≤ stageL)
    (hstageL : _root_.ThreeSum.LightRadixKeys.space stageL (_root_.ThreeSum.LightReportingPrefixArrays.localCount (464*h) h) k ≤ stageR)
    (hstageR : _root_.ThreeSum.LightRadixKeys.space stageR (_root_.ThreeSum.LightReportingPrefixArrays.localCount (464*h) h) k ≤ ptrBase)
    (hptr : ptrBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤ boxBase)
    (hbox : boxBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k*_root_.ThreeSum.LightReportingSuffixCatalog.stride ((J-k)*(464*h)) boxCut ≤ maskBase)
    (hmasks : maskBase+_root_.ThreeSum.SubsetAddress.downsetCap ((J-k)*(464*h)) boxCut ≤ work)
    (hpairSpace : work+2*(464*h)+2 ≤ lim.space)
    (hspace : work+1+_root_.ThreeSum.LightPascal.tableSize (J*(464*h))+(J*(464*h)+1) ≤ lim.space)
    (hpowWord : ((2^(464*h+1) : ℕ) : ℤ) ≤ lim.word)
    (hkeysWord : (_root_.ThreeSum.LightRadixKeys.word (2^(464*h)) (2^(464*h)) k : ℤ) ≤ lim.word)
    (hword : (((J*(464*h)+1)*2^(J*(464*h)+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^((J-k)*(464*h))*
      ((2^((J-k)*(464*h))*B)*(2^((J-k)*(464*h))*D)) : ℕ) : ℤ) ≤ lim.word)
    (hpre : k*h+boxCut ≤ cut)
    (hf : ∀ S, S.card ≤ cut → |f S| ≤ B) (hg : ∀ S, S.card ≤ cut → |g S| ≤ D)
    (hstoredL : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseL cut f (J*(464*h)))
    (hstoredR : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseR cut g (J*(464*h)))
    (hdPair : d+464*h+k+5 ≤ lim.depth) (hd : d+J*(464*h)+14 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.program 43 d
      [J*(464*h),cut,boxCut,(J-k)*(464*h),(J-k)*(464*h),k*(464*h),baseL,baseR,
        464*h,h,k,srcS,pairL,pairR,stageL,stageR,ptrBase,boxBase,maskBase,work]
      μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.time h J k boxCut)
      (fun r μ' =>
        r = (stageL+_root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum.LightReportingPrefixArrays.localCount (464*h) h) k : ℕ) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' ptrBase (List.ofFn fun i : Fin (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k) =>
          boxBase+i.val*_root_.ThreeSum.LightReportingSuffixCatalog.stride ((J-k)*(464*h)) boxCut) ∧
        (∀ i < _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k, _root_.ThreeSum.LightBoxStages.StoredThrough μ'
          (boxBase+i*_root_.ThreeSum.LightReportingSuffixCatalog.stride ((J-k)*(464*h)) boxCut) boxCut
          (_root_.ThreeSum.ReportingHostSuffix.leafWeight (_root_.ThreeSum.ReportingHostSuffix.block_fit hk) f g ((J-k)*(464*h)) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL h J k i) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR h J k i))
          ((J-k)*(464*h))) ∧
        _root_.ThreeSum.LightZetaStages.StoredThrough μ' baseL cut f (J*(464*h)) ∧
        _root_.ThreeSum.LightZetaStages.StoredThrough μ' baseR cut g (J*(464*h)) ∧
        μ' (stageL+_root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum.LightReportingPrefixArrays.localCount (464*h) h) k) =
          (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k : ℤ) ∧
        (∀ i < _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k,
          μ' (stageL+_root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum.LightReportingPrefixArrays.localCount (464*h) h) k+1+i) =
            (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL h J k i) : ℤ)) ∧
        (∀ i < _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k,
          μ' (stageR+_root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum.LightReportingPrefixArrays.localCount (464*h) h) k+1+i) =
            (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR h J k i) : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ μ' srcS) := by
  have hn := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count_pos h k
  have hstageOrder : stageL ≤ stageR := by unfold _root_.ThreeSum.LightRadixKeys.space at hstageL; omega
  have hptrOrder : stageR ≤ ptrBase := by unfold _root_.ThreeSum.LightRadixKeys.space at hstageR; omega
  have hprefixEndL : stageL+_root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum.LightReportingPrefixArrays.localCount (464*h) h) k+1+
      _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤ ptrBase := hstageL.trans hptrOrder
  have hprefixEndR : stageR+_root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum.LightReportingPrefixArrays.localCount (464*h) h) k+1+
      _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤ ptrBase := hstageR
  have hkhWord : ((k*h : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by omega : k*h ≤ lim.space)).trans hw
  have hkhWordZ : (k : ℤ)*(h : ℤ) ≤ lim.word := by simpa only [Nat.cast_mul] using hkhWord
  have hwidth : (J-k)*(464*h) ≤ J*(464*h) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 43) (by rfl : program[43]? = some (body 10 42))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.body _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.time
  have hp := ((_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixArrays.program_meets (d := d+1) (μ := μ)
    hw (by omega) hS hL hR hstageL (hstageR.trans (by omega)) hpairSpace hpowWord hkeysWord (by omega)).append
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalogSetup.program.map
        (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixArrays.program.length))).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.body 10 42]
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hp _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hp ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingPrefixArrays.time, _root_.ThreeSum.LightReportingSuffixCatalogSetup.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightReportingPrefixArrays.time, _root_.ThreeSum.LightReportingSuffixCatalogSetup.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightReportingPrefixArrays.time, _root_.ThreeSum.LightReportingSuffixCatalogSetup.time] <;> omega)
     on_goal -1 => (rintro leftHead μ₁ ⟨hhead, hcountL, hcountR, hleftArray, hrightArray, hkeepArrays⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hhead, hcountL, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count, _root_.ThreeSum.LightReportingPrefixArrays.time, _root_.ThreeSum.LightReportingSuffixCatalogSetup.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hhead, hcountL, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count, _root_.ThreeSum.LightReportingPrefixArrays.time, _root_.ThreeSum.LightReportingSuffixCatalogSetup.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hhead, hcountL, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count, _root_.ThreeSum.LightReportingPrefixArrays.time, _root_.ThreeSum.LightReportingSuffixCatalogSetup.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum.LightReportingPrefixArrays.localCount (464 * h) h) k : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hhead, _root_.ThreeSum.LightReportingPrefixArrays.time, _root_.ThreeSum.LightReportingSuffixCatalogSetup.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hhead, _root_.ThreeSum.LightReportingPrefixArrays.time, _root_.ThreeSum.LightReportingSuffixCatalogSetup.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hhead, _root_.ThreeSum.LightReportingPrefixArrays.time, _root_.ThreeSum.LightReportingSuffixCatalogSetup.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (stageR + _root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum.LightReportingPrefixArrays.localCount (464 * h) h) k : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingPrefixArrays.time, _root_.ThreeSum.LightReportingSuffixCatalogSetup.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightReportingPrefixArrays.time, _root_.ThreeSum.LightReportingSuffixCatalogSetup.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightReportingPrefixArrays.time, _root_.ThreeSum.LightReportingSuffixCatalogSetup.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (stageL + _root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum.LightReportingPrefixArrays.localCount (464 * h) h) k + 1 : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hhead, _root_.ThreeSum.LightReportingPrefixArrays.time, _root_.ThreeSum.LightReportingSuffixCatalogSetup.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hhead, _root_.ThreeSum.LightReportingPrefixArrays.time, _root_.ThreeSum.LightReportingSuffixCatalogSetup.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hhead, _root_.ThreeSum.LightReportingPrefixArrays.time, _root_.ThreeSum.LightReportingSuffixCatalogSetup.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (stageR + _root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum.LightReportingPrefixArrays.localCount (464 * h) h) k + 1 : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingPrefixArrays.time, _root_.ThreeSum.LightReportingSuffixCatalogSetup.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightReportingPrefixArrays.time, _root_.ThreeSum.LightReportingSuffixCatalogSetup.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightReportingPrefixArrays.time, _root_.ThreeSum.LightReportingSuffixCatalogSetup.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (k * h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hkhWord, hkhWordZ, _root_.ThreeSum.LightReportingPrefixArrays.time, _root_.ThreeSum.LightReportingSuffixCatalogSetup.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hkhWord, hkhWordZ, _root_.ThreeSum.LightReportingPrefixArrays.time, _root_.ThreeSum.LightReportingSuffixCatalogSetup.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hkhWord, hkhWordZ, _root_.ThreeSum.LightReportingPrefixArrays.time, _root_.ThreeSum.LightReportingSuffixCatalogSetup.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hstoredL₁ := _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch.storedThrough_of_on hstoredL
    (by intro i _ hi; exact hkeepArrays i (by omega))
  have hstoredR₁ := _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch.storedThrough_of_on hstoredR
    (by intro i _ hi; exact hkeepArrays i (by omega))
  have hc := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.meets
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalogSetup.program_meets (d := d+1) (μ := μ₁)
      (_root_.ThreeSum.ReportingHostSuffix.block_fit hk) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL h J k) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR h J k) f g hw hcut hboxCut hwidth hn
      (hdataL.trans (by omega)) (hdataR.trans (by omega)) hprefixEndL hprefixEndR hptr hbox hmasks
      hspace hword hvalueWord
      (by intro i hi; exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL_card hk (by rwa [← _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count_eq_length]))
      (by intro i hi; exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR_card hk (by rwa [← _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count_eq_length]))
      hpre hpre hf hg hstoredL₁ hstoredR₁ (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.readL hk hleftArray) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.readR hk hrightArray) (by omega))
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixArrays.program).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.body 10 42]
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count, _root_.ThreeSum.LightReportingPrefixArrays.time, _root_.ThreeSum.LightReportingSuffixCatalogSetup.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count, _root_.ThreeSum.LightReportingPrefixArrays.time, _root_.ThreeSum.LightReportingSuffixCatalogSetup.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count, _root_.ThreeSum.LightReportingPrefixArrays.time, _root_.ThreeSum.LightReportingSuffixCatalogSetup.time] <;> omega)
     on_goal -1 => (rintro result μ₂ ⟨hptrs, hboxes, hsourceL, hsourceR, hkeepCatalog⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (stageL + _root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum.LightReportingPrefixArrays.localCount (464 * h) h) k : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hhead, _root_.ThreeSum.LightReportingPrefixArrays.time, _root_.ThreeSum.LightReportingSuffixCatalogSetup.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hhead, _root_.ThreeSum.LightReportingPrefixArrays.time, _root_.ThreeSum.LightReportingSuffixCatalogSetup.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hhead, _root_.ThreeSum.LightReportingPrefixArrays.time, _root_.ThreeSum.LightReportingSuffixCatalogSetup.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  refine ⟨by simp,hptrs,hboxes,hsourceL,hsourceR,?_,?_,?_,?_⟩
  · exact (hkeepCatalog _ (by omega)).trans hcountL
  · intro i hi
    exact (hkeepCatalog _ (by omega)).trans (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.readL hk hleftArray i hi)
  · intro i hi
    exact (hkeepCatalog _ (by omega)).trans (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.readR hk hrightArray i hi)
  · intro i hi
    exact (hkeepCatalog i (by omega)).trans (hkeepArrays i hi)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.program_meets__implementation_4679c03db3) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.program_meets__implementation_4679c03db3)

#print axioms solution
