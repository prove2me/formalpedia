-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:02:51.530187+00:00
-- url     : https://prove2.me/submissions/65a2ab3b-77ec-48bc-97fb-6fe034410788

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle030
import Definitions.Def_ThreeSum1960614_Machine_Bundle031
import Definitions.Def_ThreeSum1960614_Machine_Bundle032
import Definitions.Def_ThreeSum1960614_Machine_Bundle033
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
import Mathlib.Data.Finset.Range
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
import Mathlib.Data.List.ProdSigma
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingFrontierStep_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_RawReporting_partitionWord_length
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_RawReporting_word_children
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_ReportingHostMasks_localChildren_mem
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_StoredReporting_positivePrefix_valid
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_union_sdiff
import Theorems.Thm_ThreeSum_ReportingHostMasks_blockSet_localRow
import Theorems.Thm_ThreeSum_ReportingHostMasks_querySet_step
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
namespace ThreeSum.LightBlockChildrenIndexed
end ThreeSum.LightBlockChildrenIndexed
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingStoredStep
end ThreeSum.LightReportingStoredStep
namespace ThreeSum.LightReportingSuffixBoxes
end ThreeSum.LightReportingSuffixBoxes
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.MaskDifference
end ThreeSum.MaskDifference
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
namespace ThreeSum.ReportingHostPositive
end ThreeSum.ReportingHostPositive
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
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
end ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep
end ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixBoxes
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixBoxes
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.MaskDifference
end ThreeSum1960614.Machine.ThreeSum.MaskDifference
namespace ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
end ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
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
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
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



























theorem join_card {J L : ℕ} (I : Finset (Fin J)) (u : Fin J → Finset (Fin L)) :
    (_root_.ThreeSum.BlockRows.join I u).card = ∑ i ∈ I, (u i).card := Finset.card_sigma _ _









@[simp] theorem mem_prefixIndices {J k : ℕ} {i : Fin J} :
    i ∈ _root_.ThreeSum.BlockRows.prefixIndices J k ↔ i.val < k := by simp [_root_.ThreeSum.BlockRows.prefixIndices]



end ThreeSum.BlockRows

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









theorem subsetMask_sdiff_int {L : ℕ} (Q U : Finset (Fin L)) (hU : U ⊆ Q) :
    (_root_.ThreeSum.SubsetAddress.subsetMask Q : ℤ)-(_root_.ThreeSum.SubsetAddress.subsetMask U : ℤ) = (_root_.ThreeSum.SubsetAddress.subsetMask (Q \ U) : ℤ) := by
  have h := _root_.ThreeSum.MaskDifference.subsetMask_union_sdiff Q U hU
  have hz : (_root_.ThreeSum.SubsetAddress.subsetMask U : ℤ)+(_root_.ThreeSum.SubsetAddress.subsetMask (Q \ U) : ℤ) = (_root_.ThreeSum.SubsetAddress.subsetMask Q : ℤ) := by
    exact_mod_cast h
  omega

end ThreeSum.MaskDifference

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





@[simp] theorem mem_indexSet {J L : ℕ} (S : Finset (_root_.ThreeSum.BlockRows.Coord J L)) (c : _root_.ThreeSum.BlockRows.Coord J L) :
    _root_.ThreeSum.BlockIndex.coordEquiv J L c ∈ _root_.ThreeSum.BlockIndex.indexSet S ↔ c ∈ S := by
  simp [_root_.ThreeSum.BlockIndex.indexSet]

@[simp] theorem indexSet_card {J L : ℕ} (S : Finset (_root_.ThreeSum.BlockRows.Coord J L)) :
    (_root_.ThreeSum.BlockIndex.indexSet S).card = S.card := Finset.card_map _























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





theorem suffixStage_le (J L k : ℕ) : _root_.ThreeSum.BlockIndexedQuery.suffixStage J L k ≤ J*L :=
  Nat.mul_le_mul_right L (Nat.sub_le _ _)



























section Histograms

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]



















end Histograms

end ThreeSum.BlockIndexedQuery

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

theorem prefixMask_eq_sum {J L : ℕ} (rows : Fin J → Finset (Fin L)) (k : ℕ) :
    _root_.ThreeSum.BlockMaskLayout.prefixMask rows k = ∑ i ∈ _root_.ThreeSum.BlockRows.prefixIndices J k, _root_.ThreeSum.BlockMaskLayout.rowMask rows i := _root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout.mask_join _ _



theorem prefixIndices_succ {J k : ℕ} (hk : k < J) :
    _root_.ThreeSum.BlockRows.prefixIndices J (k+1) = insert ⟨k,hk⟩ (_root_.ThreeSum.BlockRows.prefixIndices J k) := by
  ext i
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_prefixIndices,Finset.mem_insert,Fin.ext_iff]
  omega

theorem prefixMask_succ {J L k : ℕ} (rows : Fin J → Finset (Fin L)) (hk : k < J) :
    _root_.ThreeSum.BlockMaskLayout.prefixMask rows (k+1) = _root_.ThreeSum.BlockMaskLayout.prefixMask rows k+_root_.ThreeSum.BlockMaskLayout.rowMask rows ⟨k,hk⟩ := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout.prefixMask_eq_sum,_root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout.prefixIndices_succ hk,Finset.sum_insert (by simp),_root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout.prefixMask_eq_sum]
  exact Nat.add_comm _ _



theorem prefixMask_lt {J L : ℕ} (rows : Fin J → Finset (Fin L)) (k : ℕ) :
    _root_.ThreeSum.BlockMaskLayout.prefixMask rows k < 2^(J*L) := (_root_.ThreeSum.SubsetAddress.subsetMask_isMask _).1

theorem rowMask_lt {J L : ℕ} (rows : Fin J → Finset (Fin L)) (i : Fin J) :
    _root_.ThreeSum.BlockMaskLayout.rowMask rows i < 2^(J*L) := by
  have he : _root_.ThreeSum.BlockMaskLayout.prefixMask rows (i.val+1) = _root_.ThreeSum.BlockMaskLayout.prefixMask rows i.val+_root_.ThreeSum.BlockMaskLayout.rowMask rows i :=
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout.prefixMask_succ rows i.isLt
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout.prefixMask_lt rows (i.val+1)
  omega











end ThreeSum.BlockMaskLayout

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual shrinking-suffix box preprocessing for an original valid block prefix -/

namespace ThreeSum.LightReportingSuffixBoxes
open _root_.ThreeSum.LightReportingSuffixBoxes


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
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]



theorem residual_le_suffix {h J k : ℕ} : _root_.ThreeSum.LightBlockQuery.residualSize h J k ≤ _root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k := by
  exact Nat.mul_le_mul_left (J-k) (by omega)



end ThreeSum.LightReportingSuffixBoxes

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



@[simp] theorem mem_blockSet {J L : ℕ} (i j : Fin J) (S : Finset (Fin L)) (x : Fin L) :
    _root_.ThreeSum.BlockIndex.coordEquiv J L ⟨j,x⟩ ∈ _root_.ThreeSum.ReportingHostMasks.blockSet i S ↔ j = i ∧ x ∈ S := by
  simp [_root_.ThreeSum.ReportingHostMasks.blockSet]

@[simp] theorem blockSet_card {J L : ℕ} (i : Fin J) (S : Finset (Fin L)) :
    (_root_.ThreeSum.ReportingHostMasks.blockSet i S).card = S.card := by
  simp [_root_.ThreeSum.ReportingHostMasks.blockSet,_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_card]

@[simp] theorem blockSet_mask {J L : ℕ} (i : Fin J) (S : Finset (Fin L)) :
    _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.ReportingHostMasks.blockSet i S) = 2^(i.val*L)*_root_.ThreeSum.SubsetAddress.subsetMask S := by
  simp [_root_.ThreeSum.ReportingHostMasks.blockSet,_root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout.mask_join,_root_.ThreeSum.BlockMaskLayout.rowMask]













@[simp] theorem globalChildren_length {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :
    (_root_.ThreeSum.ReportingHostMasks.globalChildren i Q h).length = Q.card.choose h := by
  simp [_root_.ThreeSum.ReportingHostMasks.globalChildren]

theorem globalChildren_nodup {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :
    (_root_.ThreeSum.ReportingHostMasks.globalChildren i Q h).Nodup := _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.missingSets_nodup _ _





theorem localChildren_nodup {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :
    (_root_.ThreeSum.ReportingHostMasks.localChildren i Q h).Nodup := by
  apply (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.globalChildren_nodup i Q h).map_on
  intro S hS T hT he
  have hs := (_root_.ThreeSum.QueryCoordinates.missingSets_mem _ _ _).mp hS
  have ht := (_root_.ThreeSum.QueryCoordinates.missingSets_mem _ _ _).mp hT
  rw [← _root_.ThreeSum.ReportingHostMasks.blockSet_localRow i Q hs.1,← _root_.ThreeSum.ReportingHostMasks.blockSet_localRow i Q ht.1,he]

@[simp] theorem localChildren_length {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :
    (_root_.ThreeSum.ReportingHostMasks.localChildren i Q h).length = Q.card.choose h := by
  simp [_root_.ThreeSum.ReportingHostMasks.localChildren]















theorem blockSet_subset_query {J L k : ℕ} (Q : Fin J → Finset (Fin L)) (hk : k < J) :
    _root_.ThreeSum.ReportingHostMasks.blockSet ⟨k,hk⟩ (Q ⟨k,hk⟩) ⊆ _root_.ThreeSum.BlockIndexedQuery.querySet k Q := by
  intro x hx
  obtain ⟨⟨i,a⟩,rfl⟩ := (_root_.ThreeSum.BlockIndex.coordEquiv J L).surjective x
  obtain ⟨rfl,ha⟩ := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.mem_blockSet _ _ _ _).mp hx
  simp only [_root_.ThreeSum.BlockIndexedQuery.querySet,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.mem_indexSet,_root_.ThreeSum.BlockForced.remaining,_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join,Finset.mem_compl,_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_prefixIndices]
  exact ⟨by simp,ha⟩

theorem queryMask_step {J L k : ℕ} (Q : Fin J → Finset (Fin L)) (hk : k < J) :
    (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.querySet k Q) : ℤ)-(_root_.ThreeSum.BlockMaskLayout.rowMask Q ⟨k,hk⟩ : ℤ) =
      (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.querySet (k+1) Q) : ℤ) := by
  rw [_root_.ThreeSum.ReportingHostMasks.querySet_step Q hk]
  have he : _root_.ThreeSum.BlockMaskLayout.rowMask Q ⟨k,hk⟩ = _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.ReportingHostMasks.blockSet ⟨k,hk⟩ (Q ⟨k,hk⟩)) := by
    simp [_root_.ThreeSum.BlockMaskLayout.rowMask]
  rw [he]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.MaskDifference.subsetMask_sdiff_int _ _ (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.blockSet_subset_query Q hk)







end ThreeSum.ReportingHostMasks

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # The concrete child constructor extends the original valid reporting prefixes -/

namespace ThreeSum.LightBlockChildrenIndexed
open _root_.ThreeSum.LightBlockChildrenIndexed


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockMaskLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum.ReportingHostMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}



theorem childPrefixes_length {h J k : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (pre : List (Finset (Fin (464*h)))) (hk : k < J) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childPrefixes q pre hk).length = _root_.ThreeSum.LocalCoverBounds.groupSize h := by
  have hc : (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q ⟨k,hk⟩).card = 2*h :=
    _root_.ThreeSum.LayerCounts.mem_vertices.mp (q ⟨k,hk⟩).2.property
  simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childPrefixes,hc,_root_.ThreeSum.LocalCoverBounds.groupSize]





















end ThreeSum.LightBlockChildrenIndexed

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

theorem map_range_getD {α : Type*} (xs : List α) (fallback : α) :
    (List.range xs.length).map (fun i => xs[i]?.getD fallback) = xs := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp only [List.getElem_map,List.getElem_range,List.getElem?_eq_getElem hi',Option.getD_some]

theorem selected_map {α : Type*} (xs : List α) (fallback : α) (q : α → ℕ) :
    (_root_.ThreeSum.LightReportingFilter.selected (fun i => q (xs[i]?.getD fallback)) xs.length).map
        (fun i => xs[i]?.getD fallback) = xs.filter (fun x => 0 < q x) := by
  change ((List.range xs.length).filter
    ((fun x : α => decide (0 < q x)) ∘ (fun i => xs[i]?.getD fallback))).map
      (fun i => xs[i]?.getD fallback) = _
  rw [← List.filter_map,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.map_range_getD]

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



theorem positiveChildren_eq_filter {h J k : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (pre : List (Finset (Fin (464*h)))) (hk : k < J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.positiveChildren I w pre hk =
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childPrefixes w.2.2 pre hk).filter (fun next => 0 < _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery I w (k+1) next) := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.positiveChildren
  change (_root_.ThreeSum.LightReportingFilter.selected
    (fun i => _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery I w (k+1) ((_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childPrefixes w.2.2 pre hk)[i]?.getD [])) (_root_.ThreeSum.LocalCoverBounds.groupSize h)).map
      (fun i => (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childPrefixes w.2.2 pre hk)[i]?.getD []) = _
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childPrefixes_length w.2.2 pre hk]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.selected_map (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childPrefixes w.2.2 pre hk) [] (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery I w (k+1))



theorem frontier_valid {h J k : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (hk : k ≤ J) {pre : List (Finset (Fin (464*h)))}
    (hp : pre ∈ _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w k) : _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix w.2.2 k pre :=
  _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.positivePrefix_valid I w pre hk (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.frontier_positive _ _ hp)

theorem frontier_step {h J k : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (hk : k < J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w (k+1) =
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w k).flatMap (fun pre => _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.positiveChildren I w pre hk) := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier,_root_.ThreeSum.Reporting.frontier,List.filter_flatMap,
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.positiveChildren_eq_filter,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.children,dif_pos hk,_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childPrefixes]





end ThreeSum.ReportingHostPositive

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





@[simp] theorem slot_zero (base cap : ℕ) : _root_.ThreeSum.ReportingHostFrontierLayout.slot base cap 0=base := by simp [_root_.ThreeSum.ReportingHostFrontierLayout.slot]
theorem slot_succ (base cap k : ℕ) : _root_.ThreeSum.ReportingHostFrontierLayout.slot base cap (k+1)=_root_.ThreeSum.ReportingHostFrontierLayout.slot base cap k+4+2*cap := by
  unfold _root_.ThreeSum.ReportingHostFrontierLayout.slot; ring

theorem slot_mono {base cap i j : ℕ} (hij : i≤j) : _root_.ThreeSum.ReportingHostFrontierLayout.slot base cap i≤_root_.ThreeSum.ReportingHostFrontierLayout.slot base cap j := by
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _











variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]



theorem rootMass_eq {h J : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ)) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass I w=(_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.domain I w).card := by
  simp [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass,_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery,_root_.ThreeSum.Reporting.mass,_root_.ThreeSum.Subset.fiberMass]



theorem group_pos (h : ℕ) : 0<_root_.ThreeSum.LocalCoverBounds.groupSize h := Nat.choose_pos (by omega)

theorem capacity_pos {h J : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ)) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) :
    0<_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.capacity I w := Nat.mul_pos (by omega) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.group_pos h)

theorem mass_lt_capacity {h J : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ)) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass I w<_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.capacity I w :=
  (Nat.lt_succ_self _).trans_le (Nat.le_mul_of_pos_right _ (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.group_pos h))

theorem frontier_capacity {h J k : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ)) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)
    (hk : k≤J) : (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w k).length≤_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.capacity I w := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier_length_le_domain I w hk
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass_eq I w] at hh
  exact hh.trans (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.mass_lt_capacity I w).le

theorem expansion_capacity {h J k : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ)) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)
    (hk : k≤J) : (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w k).length*_root_.ThreeSum.LocalCoverBounds.groupSize h≤_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.capacity I w := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier_length_le_domain I w hk
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass_eq I w] at hh
  exact Nat.mul_le_mul_right (_root_.ThreeSum.LocalCoverBounds.groupSize h) (hh.trans (Nat.le_succ _))


















end ThreeSum.ReportingHostFrontierLayout

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockMaskLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
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
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum.ReportingHostMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
set_option maxHeartbeats 3500000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep.program_meets__implementation_ff01846161 {μ : ℕ→ℤ}
    {h J k baseL baseR catalogs rows root masks childL childR counts selected maskBase work depth : ℕ}
    {D : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog} (hk : k<J)
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)
    (hkey : w.1∈A ∧ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ (a w.1%pMod+_root_.ThreeSum.RawIncidences.lift w.2.1*pMod+shift)-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2)
    (hw : (lim.space : ℤ)≤lim.word)
    (HS : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Sources μ pMod shift B C b c w.2.2 baseL baseR)
    (HC : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Stored μ D (Nat.succ_le_of_lt hk) pMod shift B C b c w.2.2)
    (HB : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Bounds h J (k+1) D baseL baseR root)
    (HW : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Scratch lim h J (k+1) D B.card C.card maskBase work)
    (hmeta : _root_.ThreeSum1960614.Machine.Light.SegN μ (catalogs+5*(k+1)) (D.record h (k+1)))
    (hmetaEnd : catalogs+5*(k+1)+5≤root)
    (hrows : rows+J≤root)
    (hrow : μ (rows+k)=(_root_.ThreeSum.BlockMaskLayout.rowMask (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2) ⟨k,hk⟩ : ℤ))
    (hcap : μ (root+3)=(_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.capacity (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w : ℤ))
    (HA : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.At μ (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w root
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.capacity (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w) k)
    (hout : _root_.ThreeSum.ReportingHostFrontierLayout.slot root (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.capacity (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w) (k+2)≤ masks)
    (hmasks : masks+_root_.ThreeSum.LocalCoverBounds.groupSize h≤childL) (hchildL : childL+_root_.ThreeSum.LocalCoverBounds.groupSize h≤childR)
    (hchildR : childR+_root_.ThreeSum.LocalCoverBounds.groupSize h≤counts) (hcounts : counts+_root_.ThreeSum.LocalCoverBounds.groupSize h≤ selected)
    (hselected : selected+_root_.ThreeSum.LocalCoverBounds.groupSize h≤ maskBase)
    (hparams : J+464*h+_root_.ThreeSum.LocalCoverBounds.groupSize h+_root_.ThreeSum.LightBlockQuery.sourceCut h J≤lim.space)
    (hd : depth+2*_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+18≤lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep.program 51 depth
      [_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J,h,J,k+1,baseL,baseR,catalogs,rows,root,masks,childL,childR,counts,selected,maskBase,work,
        _root_.ThreeSum.LocalCoverBounds.groupSize h,_root_.ThreeSum.LightBlockQuery.sourceCut h J,464*h]
      μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep.time h J k D.t (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k).length)
      (fun r ν =>
        let I := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c
        r=((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w (k+1)).length : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.At ν I w root (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.capacity I w) (k+1) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν (_root_.ThreeSum.ReportingHostFrontierLayout.slot root (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.capacity I w) (k+1))) := by
  let I := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c
  let cap := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.capacity I w
  let pres := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w k
  let old := _root_.ThreeSum.ReportingHostFrontierLayout.slot root cap k
  let dest := _root_.ThreeSum.ReportingHostFrontierLayout.slot root cap (k+1)
  let catalogRow := catalogs+5*(k+1)
  let prefixCardNext := (k+1)*h
  let offsetNext := (k+1)*(464*h)
  let stageNext := _root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) (k+1)
  let residualNext := _root_.ThreeSum.LightBlockQuery.residualSize h J (k+1)
  change _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.At μ I w root cap k at HA
  change μ (root+3)=(cap : ℤ) at hcap
  change _root_.ThreeSum.ReportingHostFrontierLayout.slot root cap (k+2)≤ masks at hout
  change _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep.program 51 depth _ μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep.time h J k D.t pres.length)
    (fun r ν => r=((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w (k+1)).length : ℤ) ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.At ν I w root cap (k+1) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν dest)
  have hcapPos : 0<cap := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.capacity_pos I w
  have hprevCount : pres.length≤cap := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.frontier_capacity I w hk.le
  have hnextCount : (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w (k+1)).length≤cap := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.frontier_capacity I w (by omega)
  have hchildren : pres.length*_root_.ThreeSum.LocalCoverBounds.groupSize h≤cap := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.expansion_capacity I w hk.le
  have hrootOld : root≤old := by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.slot_zero] using (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.slot_mono (base := root) (cap := cap) (Nat.zero_le k))
  have hold : old+4+2*cap=dest := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.slot_succ root cap k).symm
  have hdest : dest+4+2*cap≤ masks := by
    have hh := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.slot_succ root cap (k+1)
    change _root_.ThreeSum.ReportingHostFrontierLayout.slot root cap (k+2)=dest+4+2*cap at hh
    rwa [hh] at hout
  have hwork := HW.masks
  have hspace := HW.space
  have hpow := HW.powers
  have hmetaT := hmeta.getElem (i := 0) (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog.record])
  have hmetaCut := hmeta.getElem (i := 1) (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog.record])
  have hmetaIndex := hmeta.getElem (i := 2) (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog.record])
  have hmetaPtr := hmeta.getElem (i := 3) (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog.record])
  have hmetaN := hmeta.getElem (i := 4) (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog.record])
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog.record,List.getElem_cons_zero,List.getElem_cons_succ,Nat.add_zero] at hmetaT hmetaCut hmetaIndex hmetaPtr hmetaN
  change μ catalogRow=(D.t : ℤ) at hmetaT
  change μ (catalogRow+1)=(D.boxCut : ℤ) at hmetaCut
  change μ (catalogRow+2)=(D.indexBase : ℤ) at hmetaIndex
  change μ (catalogRow+3)=(D.ptrBase : ℤ) at hmetaPtr
  change μ (catalogRow+4)=(_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h (k+1) : ℤ) at hmetaN
  have hmetaBound : catalogRow+5≤root := hmetaEnd
  have hmetaIndexZ : μ (((catalogRow : ℤ)+2).toNat)=(D.indexBase : ℤ) := by
    rw [show ((catalogRow : ℤ)+2).toNat=catalogRow+2 by omega]
    exact hmetaIndex
  have hmetaPtrZ : μ (((catalogRow : ℤ)+3).toNat)=(D.ptrBase : ℤ) := by
    rw [show ((catalogRow : ℤ)+3).toNat=catalogRow+3 by omega]
    exact hmetaPtr
  have hmetaNZ : μ (((catalogRow : ℤ)+4).toNat)=(_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h (k+1) : ℤ) := by
    rw [show ((catalogRow : ℤ)+4).toNat=catalogRow+4 by omega]
    exact hmetaN
  have hDindex := HB.index
  have hDptr := HB.pointers
  have ht := HW.t
  have hcut := HW.cut
  have hwidthSpace : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J≤lim.space := by omega
  have hresLe : _root_.ThreeSum.LightBlockQuery.residualSize h J (k+1)≤_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J := by
    exact (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixBoxes.residual_le_suffix (h := h) (J := J) (k := k+1)).trans
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.suffixStage_le J (464*h) (k+1))
  change residualNext≤_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J at hresLe
  change D.t≤residualNext+1 at ht
  change D.boxCut≤residualNext at hcut
  have hstageLe := _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.suffixStage_le J (464*h) (k+1)
  change stageNext≤_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J at hstageLe
  have hprefixCard : (k+1)*h≤_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J := by
    have hh := Nat.mul_le_mul_right h (Nat.succ_le_of_lt hk)
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width
    nlinarith
  have hoffset : (k+1)*(464*h)≤_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J := Nat.mul_le_mul_right _ (by omega)
  change prefixCardNext≤_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J at hprefixCard
  change offsetNext≤_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J at hoffset
  have hmask (S : Finset (Fin (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J))) : (_root_.ThreeSum.SubsetAddress.subsetMask S : ℤ)≤lim.word := by
    have hp : 2^(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J)≤(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)*2^(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1) :=
      (Nat.pow_le_pow_right (by decide) (by omega)).trans (Nat.le_mul_of_pos_left _ (by omega))
    exact (Int.ofNat_le.mpr ((_root_.ThreeSum.SubsetAddress.subsetMask_isMask S).1.le.trans hp)).trans HW.word
  have hrowWord : (_root_.ThreeSum.BlockMaskLayout.rowMask (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2) ⟨k,hk⟩ : ℤ)≤lim.word := by
    have hh := _root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout.rowMask_lt (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2) ⟨k,hk⟩
    have hb := hmask (_root_.ThreeSum.ReportingHostMasks.blockSet ⟨k,hk⟩ (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2 ⟨k,hk⟩))
    simpa [_root_.ThreeSum.BlockMaskLayout.rowMask] using hb
  have hQ := hmask (_root_.ThreeSum.BlockIndexedQuery.querySet k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2))
  have hQnext := hmask (_root_.ThreeSum.BlockIndexedQuery.querySet (k+1) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2))
  have hreadQ : μ (old+1)=(_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.querySet k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2)) : ℤ) := HA.query
  have hreadN : μ old=(pres.length : ℤ) := HA.count
  have hcapZ : μ (((root : ℤ)+3).toNat)=(cap : ℤ) := by
    rw [show ((root : ℤ)+3).toNat=root+3 by omega]
    exact hcap
  have hrowZ : μ (((rows : ℤ)+((k : ℤ)+1)).toNat-1)=
      (_root_.ThreeSum.BlockMaskLayout.rowMask (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2) ⟨k,hk⟩ : ℤ) := by
    rw [show ((rows : ℤ)+((k : ℤ)+1)).toNat-1=rows+k by omega]
    exact hrow
  have readAdd (x y : ℕ) : μ (((x : ℤ)+(y : ℤ)).toNat)=μ (x+y) := by
    congr 1 <;> omega
  have hOldCalc : (root : ℤ)+(k : ℤ)*(4+2*(cap : ℤ))=(old : ℤ) := by
    simp only [old,_root_.ThreeSum.ReportingHostFrontierLayout.slot,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  have hDestCalc : (root : ℤ)+((k : ℤ)+1)*(4+2*(cap : ℤ))=(dest : ℤ) := by
    simp only [dest,_root_.ThreeSum.ReportingHostFrontierLayout.slot,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  have hMetaCalc : (catalogs : ℤ)+5*((k : ℤ)+1)=(catalogRow : ℤ) := by
    simp only [catalogRow,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  have hSubtract : ((J-(k+1) : ℕ) : ℤ)=(J : ℤ)-((k : ℤ)+1) := by omega
  have hStageCalc : ((J : ℤ)-((k : ℤ)+1))*(464*(h : ℤ))=(stageNext : ℤ) := by
    simp only [stageNext,_root_.ThreeSum.BlockIndexedQuery.suffixStage,Nat.cast_mul,Nat.cast_sub (show k+1≤J by omega),Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
  have hResidualCalc : ((J : ℤ)-((k : ℤ)+1))*(2*(h : ℤ))=(residualNext : ℤ) := by
    simp only [residualNext,_root_.ThreeSum.LightBlockQuery.residualSize,Nat.cast_mul,Nat.cast_sub (show k+1≤J by omega),Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
  have hPrefixCalc : ((k : ℤ)+1)*(h : ℤ)=(prefixCardNext : ℤ) := by
    simp only [prefixCardNext,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  have hOffsetCalc : ((k : ℤ)+1)*(464*(h : ℤ))=(offsetNext : ℤ) := by
    simp only [offsetNext,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 51) (by rfl : program[51]?=some (body 50))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep.body _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (cap : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcapZ, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hcapZ, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcapZ, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (4 + 2 * cap : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (old : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hOldCalc, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hOldCalc, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hOldCalc, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (dest : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hDestCalc, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hDestCalc, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hDestCalc, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.BlockMaskLayout.rowMask (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2) ⟨k, hk⟩ : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrowZ, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hrowZ, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrowZ, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.querySet k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2)) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readAdd, hreadQ, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readAdd, hreadQ, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readAdd, hreadQ, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (catalogRow : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hMetaCalc, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hMetaCalc, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hMetaCalc, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (D.t : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hMetaCalc, readAdd, hmetaT, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hMetaCalc, readAdd, hmetaT, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hMetaCalc, readAdd, hmetaT, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (D.boxCut : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hMetaCalc, readAdd, hmetaCut, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hMetaCalc, readAdd, hmetaCut, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hMetaCalc, readAdd, hmetaCut, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (D.indexBase : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hMetaCalc, hmetaIndexZ, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hMetaCalc, hmetaIndexZ, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hMetaCalc, hmetaIndexZ, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (D.ptrBase : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hMetaCalc, hmetaPtrZ, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hMetaCalc, hmetaPtrZ, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hMetaCalc, hmetaPtrZ, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h (k + 1) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hMetaCalc, hmetaNZ, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hMetaCalc, hmetaNZ, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hMetaCalc, hmetaNZ, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (stageNext : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hStageCalc, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hStageCalc, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hStageCalc, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (prefixCardNext : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hPrefixCalc, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hPrefixCalc, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hPrefixCalc, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (residualNext : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hResidualCalc, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hResidualCalc, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hResidualCalc, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (offsetNext : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hOffsetCalc, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hOffsetCalc, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hOffsetCalc, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (pres.length : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadN, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hreadN, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadN, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hrun := (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.program_meets (depth := depth+1) (μ := μ)
    (inL := old+4) (inR := old+4+cap) (outL := dest+4) (outR := dest+4+cap)
    pMod shift A B C a b c w pres hk
    (fun _ hp => _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.frontier_valid I w hk.le hp) hkey hw
    (HB.left.trans (by omega)) (HB.right.trans (by omega))
    (HB.index.trans (by omega)) (HB.pointers.trans (by omega)) (HB.boxes.trans (by omega))
    (by omega) (by omega) (by omega) (by omega) hmasks hchildL hchildR hcounts hselected
    HW.masks HW.space HW.powers HW.emod HW.word HW.lookup HW.values HW.t HW.cut HW.flags
    HS.left HS.right HC.index HC.pointers HC.boxes HA.left HA.right (by omega)).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep.body 50]
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hrun _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hrun ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hSubtract, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hSubtract, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hSubtract, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;> omega)
     on_goal -1 => (rintro result ν ⟨hresult, hnewL, hnewR, hkept⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hstep := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.frontier_step I w hk
  change result=((pres.flatMap (fun pre => _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.positiveChildren I w pre hk)).length : ℤ) at hresult
  change _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveExpand.KeptOutputs μ ν masks (dest+4) (dest+4+cap)
    (pres.flatMap (fun pre => _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.positiveChildren I w pre hk)).length at hkept
  change _root_.ThreeSum1960614.Machine.Light.SegN ν (dest+4) ((pres.flatMap (fun pre => _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.positiveChildren I w pre hk)).map
    fun pre => _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.leftPrefix (k+1) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre))) at hnewL
  change _root_.ThreeSum1960614.Machine.Light.SegN ν (dest+4+cap) ((pres.flatMap (fun pre => _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.positiveChildren I w pre hk)).map
    fun pre => _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.rightPrefix (k+1) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre))) at hnewR
  have hpstep : pres.flatMap (fun pre => _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.positiveChildren I w pre hk)=
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w (k+1) := hstep.symm
  rw [hpstep] at hresult hkept hnewL hnewR
  have hnextWord : ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w (k+1)).length : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (hnextCount.trans (by omega))).trans hw
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.querySet (k + 1) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2)) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.queryMask_step, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.queryMask_step, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.queryMask_step, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen dest ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w (k + 1)).length : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hresult, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hresult, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hresult, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dest + 1) (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.querySet (k + 1) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2)) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w (k + 1)).length : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hresult, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hresult, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hresult, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFrontierStep.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  refine ⟨by simp,?_,?_⟩
  · constructor
    · change Function.update (Function.update ν dest _) (dest+1) _ dest=_
      simp
    · change Function.update (Function.update ν dest _) (dest+1) _ (dest+1)=_
      simp
    · intro i hi
      change Function.update (Function.update ν dest _) (dest+1) _ (dest+4+i)=_
      rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
      exact hnewL i hi
    · intro i hi
      change Function.update (Function.update ν dest _) (dest+1) _ (dest+4+cap+i)=_
      rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
      exact hnewR i hi
  · intro i hi
    change Function.update (Function.update ν dest _) (dest+1) _ i=μ i
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    exact hkept i ⟨by omega,Or.inl (by omega),Or.inl (by omega)⟩
end

end

theorem solution.{u_implementation_0,u_implementation_1,u_implementation_2} : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep.program_meets__implementation_ff01846161.{u_implementation_0,u_implementation_1,u_implementation_2}) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep.program_meets__implementation_ff01846161.{u_implementation_0,u_implementation_1,u_implementation_2})

#print axioms solution
