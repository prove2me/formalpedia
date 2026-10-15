-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightReportingLevels.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:02:54.298451+00:00
-- url     : https://prove2.me/submissions/13dd213e-b488-4434-9436-2f4d6272b7de

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingStoredStep_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_RawReporting_partitionWord_length
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_RawReporting_word_children
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_ReportingHostFrontierLayout_At_of_kept
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_ReportingHostLevelData_Stored_of_kept
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_ReportingHostMasks_localChildren_mem
import Theorems.Thm_ThreeSum_ReportingHostMasks_blockSet_localRow
import Theorems.Thm_ThreeSum_Reporting_frontier_length_le_mass
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
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingLevels
end ThreeSum.LightReportingLevels
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightSignedLeafBatch
end ThreeSum.LightSignedLeafBatch
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostFrontier
end ThreeSum.ReportingHostFrontier
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
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
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingLevels
end ThreeSum1960614.Machine.ThreeSum.LightReportingLevels
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch
end ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaCell
end ThreeSum1960614.Machine.ThreeSum.LightZetaCell
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
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
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier
end ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
end ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
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

/-!
# Regions of the memory, and the cells that a step leaves alone

A region is given by its first address `a` and its number `n` of cells.  `Inside a n b` says that
the cell `b` lies in it, `Outside a n b` that it does not, and `Apart a n a' n'` that two regions do
not meet.  `InOrder top [(a, n), (a', n'), …]` says that the listed regions lie one behind the other
and end at or below `top`.  All of these abbreviate linear inequalities.

`SameOn K μ μ'` says that the memory `μ'` agrees with `μ` on every cell that satisfies `K`.  It is
the one notion of "these cells are unchanged": a routine promises `SameOn K μ μ'` for the cells
`K` that it leaves alone.  (It is `Set.EqOn μ' μ {b | K b}`, stated with a predicate: the conditions
`K b` that occur are linear inequalities between addresses and are used as such.)  The usual choices
of `K` have names.

* `SameOutside μ μ' a n`: all cells outside one region; `SameOutside2` and `SameOutside3`: all cells
  outside two or three regions.
* `Kept μ μ' fr`: all cells below the free pointer `fr`.
* `KeptBut μ μ' fr out len`: all cells below `fr` outside the region of an output.

## How a fact is carried from one memory to a later one

A predicate `X` about a memory has one lemma of the name `X.keep` and of the form

  `theorem X.keep (h : X μ …) (hs : SameOn K μ μ' := by light_keep) : X μ' …`

where `K` describes the cells that `X` reads; `Seg.keep` is the model.  The argument `hs` has a
default proof.  So `h.keep`, with no argument, stands for "`h` still holds in the memory that is
asked for here".  The default proof `light_keep` uses every hypothesis of the form `SameOn _ ν ν'`
in the context, that is, the promises of the steps that were taken since `h` was obtained, and the
inequalities in the context that say where the regions lie.  In the proofs a promise is named when
the step is taken, as `same₂` in `rintro _ μ₂ ⟨sY, same₂⟩`.

`wrote μ dst f j` is the memory `μ` after a loop has written `f 0`, …, `f (j - 1)` to the cells from
`dst`.
-/

@[expose] public section

namespace Light
open _root_.Light


/-! ## Regions -/









/-! ## Memories that agree on some cells -/













variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}



theorem SameOn.refl : _root_.ThreeSum1960614.Machine.Light.SameOn K μ μ := fun _ _ => rfl









/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}















/-! ## The tactics -/











end Light

end

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





@[simp] theorem slot_zero (base cap : ℕ) : _root_.ThreeSum.ReportingHostFrontierLayout.slot base cap 0=base := by simp [_root_.ThreeSum.ReportingHostFrontierLayout.slot]


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

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLevels

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
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingLevels.program_meets__implementation_bdb32fc65e {μ : ℕ→ℤ}
    {h J K k baseL baseR catalogs rows root masks childL childR counts selected maskBase work depth : ℕ}
    (D : ℕ→_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog) (hk : k≤K) (hK : K≤J)
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)
    (hkey : w.1∈A ∧ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ (a w.1%pMod+_root_.ThreeSum.RawIncidences.lift w.2.1*pMod+shift)-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2)
    (hw : (lim.space : ℤ)≤lim.word)
    (HS : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Sources μ pMod shift B C b c w.2.2 baseL baseR)
    (HC : ∀ (j : ℕ) (hj : j≤K), _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Stored μ (D j) (hj.trans hK) pMod shift B C b c w.2.2)
    (HB : ∀ j≤K, _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Bounds h J j (D j) baseL baseR root)
    (HW : ∀ j≤K, _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Scratch lim h J j (D j) B.card C.card maskBase work)
    (hmeta : ∀ j≤K, _root_.ThreeSum1960614.Machine.Light.SegN μ (catalogs+5*j) ((D j).record h j))
    (hmetaEnd : catalogs+5*(K+1)≤root) (hrows : rows+J≤root)
    (hrow : ∀ (j : ℕ) (hj : j<J), μ (rows+j)=(_root_.ThreeSum.BlockMaskLayout.rowMask (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2) ⟨j,hj⟩ : ℤ))
    (hcap : μ (root+3)=(_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.capacity (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w : ℤ))
    (HA : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.At μ (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w root
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.capacity (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w) 0)
    (hout : _root_.ThreeSum.ReportingHostFrontierLayout.slot root (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.capacity (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w) (K+1)≤ masks)
    (hmasks : masks+_root_.ThreeSum.LocalCoverBounds.groupSize h≤childL) (hchildL : childL+_root_.ThreeSum.LocalCoverBounds.groupSize h≤childR)
    (hchildR : childR+_root_.ThreeSum.LocalCoverBounds.groupSize h≤counts) (hcounts : counts+_root_.ThreeSum.LocalCoverBounds.groupSize h≤ selected)
    (hselected : selected+_root_.ThreeSum.LocalCoverBounds.groupSize h≤ maskBase)
    (hparams : J+464*h+_root_.ThreeSum.LocalCoverBounds.groupSize h+_root_.ThreeSum.LightBlockQuery.sourceCut h J≤lim.space)
    (hd : depth+k+2*_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+19≤lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLevels.program 52 depth
      [_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J,h,J,k,baseL,baseR,catalogs,rows,root,masks,childL,childR,counts,selected,maskBase,work,
        _root_.ThreeSum.LocalCoverBounds.groupSize h,_root_.ThreeSum.LightBlockQuery.sourceCut h J,464*h]
      μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLevels.time (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w D k)
      (fun r ν =>
        let I := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c
        r=((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w k).length : ℤ) ∧
        (∀ j≤k, _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.At ν I w root (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.capacity I w) j) ∧
        ν (root+3)=(_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.capacity I w : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν root) := by
  let I := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c
  let cap := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.capacity I w
  change _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.At μ I w root cap 0 at HA
  change μ (root+3)=(cap : ℤ) at hcap
  change _root_.ThreeSum.ReportingHostFrontierLayout.slot root cap (K+1)≤ masks at hout
  change _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLevels.program 52 depth _ μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLevels.time I w D k)
    (fun r ν => r=((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w k).length : ℤ) ∧
      (∀ j≤k, _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.At ν I w root cap j) ∧ ν (root+3)=(cap : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν root)
  have hcapPos : 0<cap := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.capacity_pos I w
  have hw0 := HW 0 (Nat.zero_le K)
  have hspace := hw0.space
  have hwork := hw0.masks
  have hfirst : _root_.ThreeSum.ReportingHostFrontierLayout.slot root cap 1≤ masks := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.slot_mono (by omega)).trans hout
  have hfirst' : root+4+2*cap≤ masks := by simpa [_root_.ThreeSum.ReportingHostFrontierLayout.slot,Nat.add_assoc] using hfirst
  have hcapSpace : cap≤lim.space := by omega
  induction k generalizing depth with
  | zero =>
      apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 52) (by rfl : program[52]?=some (body 52 51))
      unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLevels.body _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLevels.time
      (focus
         ((first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
           repeat
             with_unfolding_none
               first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
         refine _root_.ThreeSum1960614.Machine.Light.Ends.iteIffThen ((0 : ℤ) < 0) (fun hbad => ?_) (fun hbase => ?_) ?_ ?_
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
      · omega
      · have hcount : μ root=((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w 0).length : ℤ) := by
          simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.slot_zero] using HA.count
        have hcountSpace := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.frontier_capacity I w (Nat.zero_le J)
        (focus
           ((first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
             repeat
               with_unfolding_none
                 first
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
           refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w 0).length : ℕ) ?_ ?_ ?_
           on_goal -1 =>
             first
             | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcount]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [hcount] <;>
                   first
                   | omega
                   | (ring_nf; omega))
           on_goal -1 =>
             ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
               (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
               simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcount] <;> omega)
           try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
        refine ⟨by simp,?_,hcap,_root_.ThreeSum1960614.Machine.Light.SameOn.refl⟩
        intro j hj
        have hj0 : j=0 := by omega
        subst j
        exact HA
  | succ k ih =>
      have hkle : k≤K := by omega
      have hkJ : k<J := by omega
      apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 52) (by rfl : program[52]?=some (body 52 51))
      unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLevels.body
      rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLevels.time]
      (focus
         ((first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
           repeat
             with_unfolding_none
               first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
         refine _root_.ThreeSum1960614.Machine.Light.Ends.iteIffThen ((0 : ℤ) < ((k + 1 : ℕ) : ℤ)) (fun hstep => ?_) (fun hbad => ?_) ?_ ?_
         on_goal -1 =>
           first
           | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep.time]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep.time] <;>
                 first
                 | omega
                 | (ring_nf; omega))
         on_goal -1 =>
           ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
             (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
             simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep.time] <;> omega)
         all_goals
           repeat
             with_unfolding_none
               first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
      · have hr := ih hkle (depth := depth+1) (by omega)
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
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hr _ (by omega)) ?_ ?_ ?_ ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hr ?_ ?_ ?_ ?_
           on_goal -1 =>
             first
             | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep.time]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep.time] <;>
                   first
                   | omega
                   | (ring_nf; omega))
           on_goal -1 => omega
           on_goal -1 =>
             ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
               (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
               simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep.time] <;> omega)
           on_goal -1 => (rintro prev ν ⟨hprev, hlevels, hcapν, hkeepν⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
        have HSν := HS.of_kept (HB 0 (by omega)) hkeepν
        have HCν := (HC (k+1) hk).of_kept (HB (k+1) hk) hkeepν
        have hmetaν : _root_.ThreeSum1960614.Machine.Light.SegN ν (catalogs+5*(k+1)) ((D (k+1)).record h (k+1)) := by
          intro i hi
          have hi' : i<5 := by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog.record,List.length_map,List.length_cons,List.length_nil] using hi
          have hm := Nat.mul_le_mul_left 5 (show k+2≤K+1 by omega)
          exact (hkeepν _ (by omega)).trans (hmeta (k+1) hk i hi)
        have hrowν : ν (rows+k)=(_root_.ThreeSum.BlockMaskLayout.rowMask (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2) ⟨k,hkJ⟩ : ℤ) :=
          (hkeepν _ (by omega)).trans (hrow k hkJ)
        have houtk : _root_.ThreeSum.ReportingHostFrontierLayout.slot root cap (k+2)≤ masks := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.slot_mono (by omega)).trans hout
        have hrun := (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep.program_meets (depth := depth+1) (μ := ν) hkJ
          pMod shift A B C a b c w hkey hw HSν HCν (HB (k+1) hk) (HW (k+1) hk)
          hmetaν (by have hm:=Nat.mul_le_mul_left 5 (show k+2≤K+1 by omega); omega)
          hrows hrowν hcapν (hlevels k le_rfl) houtk hmasks hchildL hchildR hcounts hselected hparams (by omega)).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLevels.body 52 51]
        change _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLevels.program 51 (depth+1) _ ν
          (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep.time h J k (D (k+1)).t
            (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w k).length) _ at hrun
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
             | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep.time]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep.time] <;>
                   first
                   | omega
                   | (ring_nf; omega))
           on_goal -1 => omega
           on_goal -1 =>
             ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
               (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
               simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingStoredStep.time] <;> omega)
           on_goal -1 => (rintro found ν₂ ⟨hfound, hnew, hkeepStep⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
        change found=((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w (k+1)).length : ℤ) at hfound
        change _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.At ν₂ I w root cap (k+1) at hnew
        change _root_.ThreeSum1960614.Machine.Light.Kept ν ν₂ (_root_.ThreeSum.ReportingHostFrontierLayout.slot root cap (k+1)) at hkeepStep
        have hrootStep : root+3<_root_.ThreeSum.ReportingHostFrontierLayout.slot root cap (k+1) := by
          have hh : _root_.ThreeSum.ReportingHostFrontierLayout.slot root cap 1≤_root_.ThreeSum.ReportingHostFrontierLayout.slot root cap (k+1) := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.slot_mono (by omega)
          simp only [_root_.ThreeSum.ReportingHostFrontierLayout.slot] at hh ⊢
          omega
        refine ⟨hfound,?_,(hkeepStep _ hrootStep).trans hcapν,?_⟩
        · intro j hj
          by_cases hjeq : j=k+1
          · simpa only [hjeq] using hnew
          · exact (hlevels j (by omega)).of_kept (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.frontier_capacity I w (by omega))
              (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.slot_mono (by omega)) hkeepStep
        · intro i hi
          exact (hkeepStep i (by omega)).trans (hkeepν i hi)
      · omega
end

end

theorem solution.{u_implementation_0,u_implementation_1,u_implementation_2} : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingLevels.program_meets__implementation_bdb32fc65e.{u_implementation_0,u_implementation_1,u_implementation_2}) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingLevels.program_meets__implementation_bdb32fc65e.{u_implementation_0,u_implementation_1,u_implementation_2})

#print axioms solution
