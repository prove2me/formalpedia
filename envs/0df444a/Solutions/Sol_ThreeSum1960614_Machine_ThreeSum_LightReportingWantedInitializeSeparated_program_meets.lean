-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitializeSeparated.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T08:58:32.51568+00:00
-- url     : https://prove2.me/submissions/2674267a-7220-49db-bfe5-5b8ca21f3a8b

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBlockMasks_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingInitializeStored_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_ReportingHostLevelData_Stored_of_kept
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
namespace ThreeSum.LightBlockMasks
end ThreeSum.LightBlockMasks
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightDenseGuard
end ThreeSum.LightDenseGuard
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightReportingWantedInitialize
end ThreeSum.LightReportingWantedInitialize
namespace ThreeSum.LightReportingWantedInitializeSeparated
end ThreeSum.LightReportingWantedInitializeSeparated
namespace ThreeSum.LightSignedLeafBatch
end ThreeSum.LightSignedLeafBatch
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
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
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockMasks
end ThreeSum1960614.Machine.ThreeSum.LightBlockMasks
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightDenseGuard
end ThreeSum1960614.Machine.ThreeSum.LightDenseGuard
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitialize
end ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitialize
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitializeSeparated
end ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitializeSeparated
namespace ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch
end ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaCell
end ThreeSum1960614.Machine.ThreeSum.LightZetaCell
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.MaskDecode
end ThreeSum1960614.Machine.ThreeSum.MaskDecode
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
end ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
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







/-! ## The limits -/









end Light

end

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



























@[simp] theorem packedMasks_length {J L : ℕ} (rows : Fin J → Finset (Fin L)) :
    (_root_.ThreeSum.BlockMaskLayout.packedMasks rows).length = J := by simp [_root_.ThreeSum.BlockMaskLayout.packedMasks]



end ThreeSum.BlockMaskLayout

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
# Packing physical block masks into global row-major coordinates

The fixed program builds a power table, scales every input row mask by its
block position, writes the global row masks, and returns their union mask.
Only linear scans and polynomial scratch are used.
-/

namespace ThreeSum.LightBlockMasks
open _root_.ThreeSum.LightBlockMasks


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
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

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}















theorem program_meets {μ : ℕ → ℤ} {J L src dst work d : ℕ} (rows : Fin J → Finset (Fin L))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+J ≤ work) (hdst : dst+J ≤ work) (hsep : _root_.Light.Apart src J dst J)
    (hspace : work+(L+1) ≤ lim.space)
    (hword : ((2^(J*L+1) : ℕ) : ℤ) ≤ lim.word)
    (hread : _root_.ThreeSum1960614.Machine.Light.SegN μ src (_root_.ThreeSum.BlockMaskLayout.rawMasks rows)) (hd : d+1 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockMasks.program 0 d [J,L,src,dst,work] μ (_root_.ThreeSum.LightBlockMasks.time J L)
      (fun r μ' => r = (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndex.indexSet (_root_.ThreeSum.BlockRows.flat rows)) : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' dst (_root_.ThreeSum.BlockMaskLayout.packedMasks rows) ∧ _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' work dst J) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockMasks.meets rfl rfl rows hw hsrc hdst hsep hspace hword hread hd



end ThreeSum.LightBlockMasks

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual cumulative mass guard before expensive reporting

The root header is the actual Initialize output, whose third cell contains
the queried raw mass. This procedure adds that cell to the retained running
counter and returns one exactly when the computed threshold is exceeded.
It changes only the counter cell.
-/

namespace ThreeSum.LightDenseGuard
open _root_.ThreeSum.LightDenseGuard


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light





variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {μ : ℕ→ℤ}
  {counter root old mass threshold d : ℕ}

theorem meets {p : ℕ} (hp : P[p]?=some _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseGuard.body)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hcounter : counter+1 ≤ lim.space) (hroot : root+3 ≤ lim.space)
    (hword : ((old+mass+threshold+2 : ℕ) : ℤ) ≤ lim.word)
    (hread : μ counter=(old : ℤ)) (hmass : μ (root+2)=(mass : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [counter,root,threshold] μ _root_.ThreeSum.LightDenseGuard.time
      (fun result ν => result=(if threshold < old+mass then 1 else 0 : ℤ) ∧
        ν counter=((old+mass : ℕ) : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ ν counter 1) := by
  have hmassZ : μ (((root : ℤ)+2).toNat)=(mass : ℤ) := by
    rw [show ((root : ℤ)+2).toNat=root+2 by omega]
    exact hmass
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hp
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseGuard.body _root_.ThreeSum.LightDenseGuard.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (old + mass : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hread, hmass, hmassZ]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hread, hmass, hmassZ] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hread, hmass, hmassZ] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen counter (old + mass : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.iteIffThen (threshold < old + mass) (fun hyes => ?_) (fun hno => ?_) ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
     all_goals
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
  · (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (1 : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    exact ⟨by simp [hyes],by simp,by 
        (( try refine _root_.ThreeSum1960614.Machine.Light.SameOn.cell ?_
           intro p2m_macro_3398531665937738636 p2m_macro_1240400179407985249
           first
           | ((  repeat ((with_reducible rename _root_.ThreeSum1960614.Machine.Light.SameOn _ _ _ => p2m_macro_5848849775758747573); (try have := p2m_macro_5848849775758747573 p2m_macro_3398531665937738636 (by omega)); revert p2m_macro_5848849775758747573)
                 intros
                 try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
           |
             (simp [] at p2m_macro_1240400179407985249;
               ( repeat ((with_reducible rename _root_.ThreeSum1960614.Machine.Light.SameOn _ _ _ => p2m_macro_13185840165751173247); (try have := p2m_macro_13185840165751173247 p2m_macro_3398531665937738636 (by omega)); revert p2m_macro_13185840165751173247)
                 intros
                 try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
           | ( ( repeat ((with_reducible rename _root_.ThreeSum1960614.Machine.Light.SameOn _ _ _ => p2m_macro_9981139781023521788); (try have := p2m_macro_9981139781023521788 p2m_macro_3398531665937738636 (by omega)); revert p2m_macro_9981139781023521788)
                 intros
                 try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
               fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                           SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                           its condition K x does not follow from the hypotheses.")))⟩
  · (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    exact ⟨by simp [hno],by simp,by 
        (( try refine _root_.ThreeSum1960614.Machine.Light.SameOn.cell ?_
           intro p2m_macro_1697103573626966269 p2m_macro_10856951171528071080
           first
           | ((  repeat ((with_reducible rename _root_.ThreeSum1960614.Machine.Light.SameOn _ _ _ => p2m_macro_17921558102856351201); (try have := p2m_macro_17921558102856351201 p2m_macro_1697103573626966269 (by omega)); revert p2m_macro_17921558102856351201)
                 intros
                 try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
           |
             (simp [] at p2m_macro_10856951171528071080;
               ( repeat ((with_reducible rename _root_.ThreeSum1960614.Machine.Light.SameOn _ _ _ => p2m_macro_10669375618297626363); (try have := p2m_macro_10669375618297626363 p2m_macro_1697103573626966269 (by omega)); revert p2m_macro_10669375618297626363)
                 intros
                 try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
           | ( ( repeat ((with_reducible rename _root_.ThreeSum1960614.Machine.Light.SameOn _ _ _ => p2m_macro_14235828046668935949); (try have := p2m_macro_14235828046668935949 p2m_macro_1697103573626966269 (by omega)); revert p2m_macro_14235828046668935949)
                 intros
                 try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
               fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                           SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                           its condition K x does not follow from the hypotheses.")))⟩



theorem program_meets (hw : (lim.space : ℤ) ≤ lim.word)
    (hcounter : counter+1 ≤ lim.space) (hroot : root+3 ≤ lim.space)
    (hword : ((old+mass+threshold+2 : ℕ) : ℤ) ≤ lim.word)
    (hread : μ counter=(old : ℤ)) (hmass : μ (root+2)=(mass : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseGuard.program 0 d [counter,root,threshold] μ _root_.ThreeSum.LightDenseGuard.time
      (fun result ν => result=(if threshold < old+mass then 1 else 0 : ℤ) ∧
        ν counter=((old+mass : ℕ) : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ ν counter 1) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseGuard.meets rfl hw hcounter hroot hword hread hmass

end ThreeSum.LightDenseGuard

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


















@[simp] theorem query_zero {J L : ℕ} (Q : Fin J→Finset (Fin L)) :
    _root_.ThreeSum.BlockIndexedQuery.querySet 0 Q=_root_.ThreeSum.BlockIndex.indexSet (_root_.ThreeSum.BlockRows.flat Q) := by
  simp [_root_.ThreeSum.BlockIndexedQuery.querySet,_root_.ThreeSum.BlockForced.remaining,_root_.ThreeSum.BlockRows.prefixIndices,_root_.ThreeSum.BlockRows.flat]

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]


































end ThreeSum.ReportingHostFrontierLayout

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact retained catalog and scratch interfaces for the level loop

These records collect the memory assertions already produced by the actual
prefix-catalog constructor. They contain no assumed query procedure. The
query adapter below invokes the existing closed, verified catalog program.
-/

namespace ThreeSum.ReportingHostLevelData
open _root_.ThreeSum.ReportingHostLevelData


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
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false





variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]









theorem Bounds.mono {h J k baseL baseR stop stop' : ℕ} {D : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Bounds h J k D baseL baseR stop) (hle : stop≤ stop') :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Bounds h J k D baseL baseR stop' :=
  ⟨H.left.trans hle,H.right.trans hle,H.index.trans hle,H.pointers.trans hle,H.boxes.trans hle⟩

theorem Sources.of_kept {h J k baseL baseR stop : ℕ} {μ ν : ℕ→ℤ} {D : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog}
    {pMod shift : ℤ} {B : Finset β} {C : Finset γ} {b : β→ℤ} {c : γ→ℤ} {q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Sources μ pMod shift B C b c q baseL baseR) (HB : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Bounds h J k D baseL baseR stop)
    (hkeep : _root_.ThreeSum1960614.Machine.Light.Kept μ ν stop) : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Sources ν pMod shift B C b c q baseL baseR := by
  constructor
  · exact _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch.storedThrough_of_on H.left
      (by intro i _ hi; exact hkeep i (hi.trans_le HB.left))
  · exact _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch.storedThrough_of_on H.right
      (by intro i _ hi; exact hkeep i (hi.trans_le HB.right))





end ThreeSum.ReportingHostLevelData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Executed wanted-mask packing, root query, and cumulative guard

The program packs the decoded original query rows, initializes the actual
root frontier using persistent catalogs, and updates the running mass
counter before any proportional traversal. Its Boolean result is exactly
the actual threshold comparison. The global guard-soundness theorem can
therefore certify this early branch on the original owner domain.
-/

namespace ThreeSum.LightReportingWantedInitialize
open _root_.ThreeSum.LightReportingWantedInitialize


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
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
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout

set_option maxHeartbeats 3800000
set_option maxRecDepth 14000
set_option linter.unusedSectionVars false








variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem frontier_of_above {μ ν : ℕ→ℤ} {h J root cap k : ℕ}
    {I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ)} {w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.At μ I w root cap k) (hkeep : ∀ i, root ≤ i → ν i=μ i) : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.At ν I w root cap k := by
  constructor
  · exact (hkeep _ (by unfold _root_.ThreeSum.ReportingHostFrontierLayout.slot; omega)).trans H.count
  · exact (hkeep _ (by unfold _root_.ThreeSum.ReportingHostFrontierLayout.slot; omega)).trans H.query
  · intro i hi
    exact (hkeep _ (by unfold _root_.ThreeSum.ReportingHostFrontierLayout.left _root_.ThreeSum.ReportingHostFrontierLayout.slot; omega)).trans (H.left i hi)
  · intro i hi
    exact (hkeep _ (by unfold _root_.ThreeSum.ReportingHostFrontierLayout.right _root_.ThreeSum.ReportingHostFrontierLayout.left _root_.ThreeSum.ReportingHostFrontierLayout.slot; omega)).trans (H.right i hi)



end ThreeSum.LightReportingWantedInitialize

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitializeSeparated

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
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
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitialize
set_option maxHeartbeats 3800000
set_option maxRecDepth 14000
set_option linter.unusedSectionVars false
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitializeSeparated.program_meets__implementation_102c94a781 {μ : ℕ→ℤ}
    {h J baseL baseR catalogs cover rawRows rows counter root maskBase work old threshold d : ℕ} {D : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog}
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)
    (hkey : w.1∈A ∧ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ (a w.1%pMod+_root_.ThreeSum.RawIncidences.lift w.2.1*pMod+shift)-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2)
    (hw : (lim.space : ℤ)≤lim.word)
    (HS : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Sources μ pMod shift B C b c w.2.2 baseL baseR)
    (HC : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Stored μ D (Nat.zero_le J) pMod shift B C b c w.2.2)
    (HB : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Bounds h J 0 D baseL baseR rows)
    (HW : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Scratch lim h J 0 D B.card C.card maskBase work)
    (hmeta : _root_.ThreeSum1960614.Machine.Light.SegN μ catalogs (D.record h 0)) (hmetaEnd : catalogs+5≤rows)
    (hgroup : μ (cover+3)=(_root_.ThreeSum.LocalCoverBounds.groupSize h : ℤ)) (hcoverEnd : cover+4≤rows)
    (hraw : rawRows+J≤rows) (hrows : rows+J≤root) (hcounter : counter+2≤rawRows)
    (hout : _root_.ThreeSum.ReportingHostFrontierLayout.slot root (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.capacity (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w) 1≤ maskBase)
    (hpackSpace : work+(464*h+1)≤lim.space)
    (hword : ((old+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w+threshold+2 : ℕ) : ℤ)≤lim.word)
    (hreadRaw : _root_.ThreeSum1960614.Machine.Light.SegN μ rawRows (_root_.ThreeSum.BlockMaskLayout.rawMasks (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2)))
    (hcounterRead : μ counter=(old : ℤ)) (hthreshold : μ (counter+1)=(threshold : ℤ))
    (hd : d+2*_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+16≤lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitialize.program 41 d
      [_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J,_root_.ThreeSum.LightBlockQuery.sourceCut h J,J,464*h,baseL,baseR,catalogs,rawRows,rows,cover,counter,root,maskBase,work]
      μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitialize.time h J D.t)
      (fun result ν =>
        let I := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c
        result=(if threshold<old+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass I w then 1 else 0 : ℤ) ∧
        ν counter=((old+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass I w : ℕ) : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.At ν I w root (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.capacity I w) 0 ∧
        ν (root+2)=(_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass I w : ℤ) ∧ ν (root+3)=(_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.capacity I w : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN ν rows (_root_.ThreeSum.BlockMaskLayout.packedMasks (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2)) ∧ _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν rows counter 1) := by
  let I := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c
  have hwork := HW.masks
  have hspace := HW.space
  have hout' : root+4+2*_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.capacity I w≤ maskBase := by simpa [_root_.ThreeSum.ReportingHostFrontierLayout.slot,Nat.add_assoc] using hout
  have hpackWord : ((2^(J*(464*h)+1) : ℕ) : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (Nat.le_mul_of_pos_left _ (by omega))).trans HW.word
  have hthresholdZ : μ (((counter : ℤ)+1).toNat)=(threshold : ℤ) := by
    rw [show ((counter : ℤ)+1).toNat=counter+1 by omega]
    exact hthreshold
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 41) (by rfl : program[41]?=some (body 0 39 40))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitialize.body _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitialize.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (threshold : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hthreshold, hthresholdZ, _root_.ThreeSum.LightBlockMasks.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingInitializeStored.time, _root_.ThreeSum.LightDenseGuard.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hthreshold, hthresholdZ, _root_.ThreeSum.LightBlockMasks.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingInitializeStored.time, _root_.ThreeSum.LightDenseGuard.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hthreshold, hthresholdZ, _root_.ThreeSum.LightBlockMasks.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingInitializeStored.time, _root_.ThreeSum.LightDenseGuard.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hpack := (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockMasks.program_meets (μ := μ) (d := d+1) (src := rawRows) (dst := rows) (work := work)
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2) hw (by omega) (by omega) (Or.inl hraw) hpackSpace hpackWord hreadRaw (by omega)).append
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingInitializeStored.program.map (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate 2) ++
        _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseGuard.program.map (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate 40) ++ [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitialize.body 0 39 40])
  change _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitialize.program 0 (d+1) _ μ (_root_.ThreeSum.LightBlockMasks.time J (464*h)) _ at hpack
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hpack _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hpack ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBlockMasks.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingInitializeStored.time, _root_.ThreeSum.LightDenseGuard.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBlockMasks.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingInitializeStored.time, _root_.ThreeSum.LightDenseGuard.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBlockMasks.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingInitializeStored.time, _root_.ThreeSum.LightDenseGuard.time] <;> omega)
     on_goal -1 => (rintro qmask ν₁ ⟨hQ, hpacked, hkeepPack⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hkeepPackRows : _root_.ThreeSum1960614.Machine.Light.Kept μ ν₁ rows := by
    intro i hi
    exact hkeepPack i ⟨by omega,Or.inl hi⟩
  have HS₁ := HS.of_kept HB hkeepPackRows
  have HC₁ := HC.of_kept HB hkeepPackRows
  have hmeta₁ : _root_.ThreeSum1960614.Machine.Light.SegN ν₁ catalogs (D.record h 0) := by
    intro i hi
    have hi' : i<5 := by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog.record,List.length_map,List.length_cons,List.length_nil] using hi
    exact (hkeepPackRows _ (by omega)).trans (hmeta i hi)
  have hgroup₁ : ν₁ (cover+3)=(_root_.ThreeSum.LocalCoverBounds.groupSize h : ℤ) :=
    (hkeepPackRows _ (by omega)).trans hgroup
  have hinit := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingInitializeStored.program_meets (μ := ν₁) (depth := d+1)
    pMod shift A B C a b c w hkey hw HS₁ HC₁ (HB.mono (by omega)) HW
    hmeta₁ (by omega) hgroup₁ (by omega) hout (by omega)
  have hinitRun := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.meets hinit _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockMasks.program).append
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseGuard.program.map (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate 40) ++ [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitialize.body 0 39 40])
  change _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitialize.program 39 (d+1) _ ν₁ (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingInitializeStored.time h J D.t) _ at hinitRun
  have hQzero : _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.querySet 0 (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2))=
      _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndex.indexSet (_root_.ThreeSum.BlockRows.flat (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2))) := by rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.query_zero]
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hinitRun _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hinitRun ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hQ, hQzero, _root_.ThreeSum.LightBlockMasks.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingInitializeStored.time, _root_.ThreeSum.LightDenseGuard.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hQ, hQzero, _root_.ThreeSum.LightBlockMasks.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingInitializeStored.time, _root_.ThreeSum.LightDenseGuard.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hQ, hQzero, _root_.ThreeSum.LightBlockMasks.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingInitializeStored.time, _root_.ThreeSum.LightDenseGuard.time] <;> omega)
     on_goal -1 => (rintro unused ν₂ ⟨_, hfrontier, hmass, hcap, hkeepInit⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  change _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.At ν₂ I w root (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.capacity I w) 0 at hfrontier
  change ν₂ (root+2)=(_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass I w : ℤ) at hmass
  change ν₂ (root+3)=(_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.capacity I w : ℤ) at hcap
  have hcounter₂ : ν₂ counter=(old : ℤ) := by
    refine (hkeepInit _ (by omega)).trans ?_
    exact (hkeepPackRows _ (by omega)).trans hcounterRead
  have hguard := _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseGuard.program_meets (μ := ν₂) (d := d+1)
    hw (by omega) (by omega) hword hcounter₂ hmass
  have hguardRun := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.meets hguard _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitialize.initialLibraries).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitialize.body 0 39 40]
  change _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitialize.program 40 (d+1) _ ν₂ _root_.ThreeSum.LightDenseGuard.time _ at hguardRun
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hguardRun _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hguardRun ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBlockMasks.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingInitializeStored.time, _root_.ThreeSum.LightDenseGuard.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBlockMasks.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingInitializeStored.time, _root_.ThreeSum.LightDenseGuard.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBlockMasks.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingInitializeStored.time, _root_.ThreeSum.LightDenseGuard.time] <;> omega)
     on_goal -1 => (rintro result ν₃ ⟨hresult, hcounter₃, hkeepGuard⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hkeepAbove : ∀ i, root ≤ i → ν₃ i=ν₂ i := fun i hi => hkeepGuard i (Or.inr (by omega))
  refine ⟨hresult,hcounter₃,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitialize.frontier_of_above hfrontier hkeepAbove,
    (hkeepAbove _ (by omega)).trans hmass,(hkeepAbove _ (by omega)).trans hcap,?_,?_⟩
  · intro i hi
    have hi' : i<J := by simpa only [List.length_map,_root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout.packedMasks_length] using hi
    exact (hkeepGuard _ (Or.inr (by omega))).trans ((hkeepInit _ (by omega)).trans (hpacked i hi))
  · intro i hi
    exact (hkeepGuard _ hi.2).trans
      ((hkeepInit _ (by omega)).trans (hkeepPackRows i hi.1))
end

end

theorem solution.{u_implementation_0,u_implementation_1,u_implementation_2} : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitializeSeparated.program_meets__implementation_102c94a781.{u_implementation_0,u_implementation_1,u_implementation_2}) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitializeSeparated.program_meets__implementation_102c94a781.{u_implementation_0,u_implementation_1,u_implementation_2})

#print axioms solution
