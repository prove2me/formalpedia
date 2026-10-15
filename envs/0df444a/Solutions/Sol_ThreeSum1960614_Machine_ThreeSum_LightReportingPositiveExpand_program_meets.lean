-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveExpand.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:44:32.071996+00:00
-- url     : https://prove2.me/submissions/bd335658-ce40-4d3c-b700-68b0202e5bca

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingCatalogExpand_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingPositiveMasks_program_meets

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
namespace ThreeSum.LightReportingFilter
end ThreeSum.LightReportingFilter
namespace ThreeSum.LightReportingPositiveExpand
end ThreeSum.LightReportingPositiveExpand
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
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
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
end ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingFilter
end ThreeSum1960614.Machine.ThreeSum.LightReportingFilter
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveExpand
end ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveExpand
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks
end ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
end ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive
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

/-- More time and a weaker conclusion. -/
theorem Meets.mono (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (hT : T ≤ T') (hR : ∀ r μ', R r μ' → R' r μ') :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T' R' := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, hp, he.mono hT fun _ => hR _ _⟩

/-- A specification holds with every larger bound on the time. -/
theorem Meets.mono_time (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (hT : T ≤ T' := by omega) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T' R :=
  h.mono hT fun _ _ hR => hR



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
# Actual positive-query filtering for a reporting frontier

The scan writes exactly the indices of positive stored query counts, in input
order. Its cost is linear in the candidate count, and original input arrays
are preserved. It does not recompute or assume the query implementation.
-/

namespace ThreeSum.LightReportingFilter
open _root_.ThreeSum.LightReportingFilter


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}





theorem selected_length_le (count : ℕ → ℕ) (j : ℕ) : (_root_.ThreeSum.LightReportingFilter.selected count j).length ≤ j := by
  exact (List.length_filter_le _ _).trans_eq List.length_range























end ThreeSum.LightReportingFilter

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

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveExpand

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
open _root_.ThreeSum.ReportingHostMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks
set_option maxHeartbeats 2200000
set_option maxRecDepth 8000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveExpand.program_meets__implementation_b69a8c3055
    {μ : ℕ → ℤ} {h J k t baseL baseR boxCut boxBase indexBase ptrBase outL outR masks dstL dstR dst selected maskBase work depth : ℕ}
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)
    (pre : List (Finset (Fin (464*h)))) (hk : k < J) (hp : _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix w.2.2 k pre)
    (hkey : w.1 ∈ A ∧ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣
      (a w.1 % pMod+_root_.ThreeSum.RawIncidences.lift w.2.1*pMod+shift)-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdataL : baseL+(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)*_root_.ThreeSum.SubsetAddress.downsetCap (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (_root_.ThreeSum.LightBlockQuery.sourceCut h J) ≤ outL)
    (hdataR : baseR+(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)*_root_.ThreeSum.SubsetAddress.downsetCap (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (_root_.ThreeSum.LightBlockQuery.sourceCut h J) ≤ outL)
    (hindex : indexBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h (k+1) ≤ outL) (hptr : ptrBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h (k+1) ≤ outL)
    (hboxesEnd : boxBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h (k+1)*_root_.ThreeSum.LightReportingSuffixCatalog.stride (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) (k+1)) boxCut ≤ outL)
    (houtL : outL+_root_.ThreeSum.LocalCoverBounds.groupSize h ≤ outR) (houtR : outR+_root_.ThreeSum.LocalCoverBounds.groupSize h ≤ masks)
    (hmasks : masks+_root_.ThreeSum.LocalCoverBounds.groupSize h ≤ dstL) (hleft : dstL+_root_.ThreeSum.LocalCoverBounds.groupSize h ≤ dstR)
    (hright : dstR+_root_.ThreeSum.LocalCoverBounds.groupSize h ≤ dst) (hdst : dst+_root_.ThreeSum.LocalCoverBounds.groupSize h ≤ selected)
    (hselected : selected+_root_.ThreeSum.LocalCoverBounds.groupSize h ≤ maskBase)
    (hqueryMasks : maskBase+_root_.ThreeSum.LightSparseQuery.queryItems (_root_.ThreeSum.LightBlockQuery.residualSize h J (k+1)) t ≤ work)
    (hspace : work+1+_root_.ThreeSum.LightPascal.tableSize (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J)+(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1) ≤ lim.space)
    (hpowSpace : work+(2*_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+2) ≤ lim.space)
    (hemodSpace : work+(Nat.log 2 (_root_.ThreeSum.LightReportingCatalogLookup.valueBound (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h (k+1))+1)+2) ≤ lim.space)
    (hword : (((_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)*2^(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1) : ℕ) : ℤ) ≤ lim.word)
    (hlookupWord : (_root_.ThreeSum.LightReportingCatalogLookup.word (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h (k+1)) : ℤ) ≤ lim.word)
    (hvalueWord : (_root_.ThreeSum.LightSparseQuery.magnitudeBound (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) (k+1)) (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) (k+1))
      (_root_.ThreeSum.LightBlockQuery.residualSize h J (k+1)) t B.card C.card : ℤ) ≤ lim.word)
    (ht : t ≤ _root_.ThreeSum.LightBlockQuery.residualSize h J (k+1)+1) (hboxCut : boxCut ≤ _root_.ThreeSum.LightBlockQuery.residualSize h J (k+1))
    (hflags : _root_.ThreeSum.LightBlockQuery.residualSize h J (k+1)-t ≤ boxCut)
    (hstoredL : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseL (_root_.ThreeSum.LightBlockQuery.sourceCut h J)
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource pMod B b w.2.2) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J))
    (hstoredR : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseR (_root_.ThreeSum.LightBlockQuery.sourceCut h J)
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource pMod shift C c w.2.2) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J))
    (hindexData : ∃ S : List ℤ, _root_.ThreeSum1960614.Machine.Light.Seg μ indexBase S ∧
      S.Perm (_root_.ThreeSum.ReportingHostPackedCatalog.codes (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog.prefixKey h J (k+1)) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h (k+1))) ∧
      S.Pairwise (· ≤ ·))
    (hptrs : _root_.ThreeSum1960614.Machine.Light.SegN μ ptrBase (List.ofFn fun i : Fin (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h (k+1)) =>
      boxBase+i.val*_root_.ThreeSum.LightReportingSuffixCatalog.stride (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) (k+1)) boxCut))
    (hboxes : ∀ i < _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h (k+1), _root_.ThreeSum.LightBoxStages.StoredThrough μ
      (boxBase+i*_root_.ThreeSum.LightReportingSuffixCatalog.stride (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) (k+1)) boxCut) boxCut
      (_root_.ThreeSum.ReportingHostSuffix.leafWeight (_root_.ThreeSum.ReportingHostSuffix.block_fit (Nat.succ_le_of_lt hk)) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource pMod B b w.2.2) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource pMod shift C c w.2.2)
        (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) (k+1)) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL h J (k+1) i) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR h J (k+1) i))
      (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) (k+1)))
    (hd : depth+2*_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+16 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveExpand.program 49 depth
      [_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J,h,_root_.ThreeSum.BlockMaskLayout.rowMask (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2) ⟨k,hk⟩,
        _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.leftPrefix k (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre)),
        _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.rightPrefix k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre)),
        _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.querySet k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2)),masks,dstL,dstR,work,
        _root_.ThreeSum.LightBlockQuery.sourceCut h J,_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) (k+1),(k+1)*h,_root_.ThreeSum.LightBlockQuery.residualSize h J (k+1),
        t,baseL,baseR,boxCut,indexBase,ptrBase,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h (k+1),_root_.ThreeSum.LocalCoverBounds.groupSize h,dst,selected,maskBase,(k+1)*(464*h),outL,outR]
      μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveExpand.time h J k t)
      (fun r ν =>
        let pos := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.positiveChildren (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w pre hk
        r = (pos.length : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN ν outL (pos.map fun next => _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.leftPrefix (k+1) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) next))) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN ν outR (pos.map fun next =>
          _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.rightPrefix (k+1) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) next))) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveExpand.KeptOutputs μ ν masks outL outR pos.length) := by
  let I := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c
  have hlen := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFilter.selected_length_le
    (fun i => _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery I w (k+1) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.childAt w.2.2 pre hk i)) (_root_.ThreeSum.LocalCoverBounds.groupSize h)
  change (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length ≤ _root_.ThreeSum.LocalCoverBounds.groupSize h at hlen
  have hposLen : (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.positiveChildren I w pre hk).length = (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length := by
    simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.positiveChildren,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices,List.length_map]
  have hmaskWord : ((2^(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1) : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.le_mul_of_pos_left _ (by omega))).trans hword
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 49) (by rfl : program[49]? = some (body 46 48))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveExpand.body _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveExpand.time
  have he := ((_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand.program_meets (depth := depth+1) (μ := μ)
    pMod shift A B C a b c w pre hk hp hkey hw (by omega) (by omega) (by omega) (by omega)
    (by omega) hmasks hleft hright hdst hselected hqueryMasks hspace hpowSpace hemodSpace hword hlookupWord
    hvalueWord ht hboxCut hflags hstoredL hstoredR hindexData hptrs hboxes (by omega)).append
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingGatherPair.program.map
        (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand.program.length))).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveExpand.body 46 48]
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (he _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen he ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand.time, _root_.ThreeSum.LightReportingGatherPair.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand.time, _root_.ThreeSum.LightReportingGatherPair.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand.time, _root_.ThreeSum.LightReportingGatherPair.time] <;> omega)
     on_goal -1 => (rintro found μ₁ ⟨hfound, hindices, hcounts, hchildren, hchildL, hchildR, hkeepExpand⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  change found = ((_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length : ℤ) at hfound
  have htime : _root_.ThreeSum.LightReportingGatherPair.time (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length ≤
      _root_.ThreeSum.LightReportingGatherPair.time (_root_.ThreeSum.LocalCoverBounds.groupSize h) := by
    unfold _root_.ThreeSum.LightReportingGatherPair.time _root_.ThreeSum.LightReportingGather.time
    omega
  have hg := ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.meets
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.program_meets (d := depth+1) (μ := μ₁)
      (indices := selected) (srcL := dstL) (srcR := dstR) (dstL := outL) (dstR := outR)
      I w pre hk hw (by omega) (by omega) (by omega) (by omega) (by omega)
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inr (by omega)) (Or.inl (by omega)) hindices hchildL hchildR hmaskWord (by omega))
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand.program).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveExpand.body 46 48]).mono_time htime
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hg _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hg ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hfound, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand.time, _root_.ThreeSum.LightReportingGatherPair.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hfound, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand.time, _root_.ThreeSum.LightReportingGatherPair.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hfound, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand.time, _root_.ThreeSum.LightReportingGatherPair.time] <;> omega)
     on_goal -1 => (rintro ret μ₂ ⟨hleftOut, hrightOut, hkeepGather⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices I w pre hk).length : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hfound, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand.time, _root_.ThreeSum.LightReportingGatherPair.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hfound, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand.time, _root_.ThreeSum.LightReportingGatherPair.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hfound, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand.time, _root_.ThreeSum.LightReportingGatherPair.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  refine ⟨by simp [I,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.positiveChildren,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveMasks.selectedIndices],hleftOut,hrightOut,?_⟩
  intro i hi
  rw [hposLen] at hi
  exact (hkeepGather i ⟨hi.2.1,hi.2.2⟩).trans (hkeepExpand i hi.1)
end

end

theorem solution.{u_implementation_0,u_implementation_1,u_implementation_2} : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveExpand.program_meets__implementation_b69a8c3055.{u_implementation_0,u_implementation_1,u_implementation_2}) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveExpand.program_meets__implementation_b69a8c3055.{u_implementation_0,u_implementation_1,u_implementation_2})

#print axioms solution
