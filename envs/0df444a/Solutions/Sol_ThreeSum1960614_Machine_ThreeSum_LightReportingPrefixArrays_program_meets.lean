-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixArrays.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:07:20.170986+00:00
-- url     : https://prove2.me/submissions/34069600-1e03-4333-bf80-2750e94a52d1

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
import Theorems.Thm_ThreeSum1960614_Machine_Light_powTable_ends
import Theorems.Thm_Light_seg_append
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightRadixKeys_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingPairRows_program_meets
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_leftAt_card
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_lefts_length
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_pairs_length
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_rights_length

private theorem platform_seg_append_e5df73c84b {μ : ℕ → ℤ} {a : ℕ} {l₁ l₂ : List ℤ} :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a (l₁ ++ l₂) ↔ _root_.ThreeSum1960614.Machine.Light.Seg μ a l₁ ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ (a + l₁.length) l₂ := by
  exact _root_.Light.seg_append

@[simp] private theorem platform_seg_nil_e5df73c84b (μ : ℕ → ℤ) (a : ℕ) :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a [] := by
  intro i h
  exact (Nat.not_lt_zero i h).elim


namespace Finset
end Finset
namespace Light
end Light
namespace Light.PowTable
end Light.PowTable
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LayerCounts
end ThreeSum.LayerCounts
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingPrefixArrays
end ThreeSum.LightReportingPrefixArrays
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSum.ReportingHostPairEnumeration
end ThreeSum.ReportingHostPairEnumeration
namespace ThreeSum.ReportingHostPairSegments
end ThreeSum.ReportingHostPairSegments
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.PowTable
end ThreeSum1960614.Machine.Light.PowTable
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LayerCounts
end ThreeSum1960614.Machine.ThreeSum.LayerCounts
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixArrays
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixArrays
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LocalGraph
end ThreeSum1960614.Machine.ThreeSum.LocalGraph
namespace ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
end ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPairSegments
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPairSegments
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

namespace ThreeSum1960614.Machine

/-!
# Exact counts for the local subset graph

These are counts of the executable finite sets used by the graph, rather
than abstract numerical cardinality hypotheses.  An edge is an ordered
pair of disjoint `h`-subsets of `Fin L`.
-/

namespace ThreeSum.LayerCounts
open _root_.ThreeSum.LayerCounts


open _root_.Finset

















theorem vertex_degree_identity (L h : ℕ) :
    L.choose h * (L - h).choose h = L.choose (2 * h) * (2 * h).choose h := by
  simpa [show 2 * h - h = h by omega] using
    (Nat.choose_mul (n := L) (k := 2 * h) (s := h) (by omega)).symm



end ThreeSum.LayerCounts

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
# Exact product-list semantics for global radix-key construction

The key list retains every local occurrence, even when several records have
the same integer key. Each stage prepends one local record and computes its
positional hash. This is the order used by the concrete row constructor.
-/

namespace ThreeSum.RadixKeyLists
open _root_.ThreeSum.RadixKeyLists


variable {α β : Type*}





theorem step_length (p : ℤ) (base prev : List ℤ) :
    (_root_.ThreeSum.RadixKeyLists.step p base prev).length=base.length*prev.length :=
  _root_.ThreeSum.RadixKeyLists.flatMap_length_uniform base _ prev.length (by simp)





theorem values_length (p : ℤ) (base : List ℤ) (j : ℕ) :
    (_root_.ThreeSum.RadixKeyLists.values p base j).length=base.length^j := by
  induction j with
  | zero => simp [_root_.ThreeSum.RadixKeyLists.values]
  | succ j ih => rw [_root_.ThreeSum.RadixKeyLists.values,_root_.ThreeSum1960614.Machine.ThreeSum.RadixKeyLists.step_length,ih,pow_succ']













end ThreeSum.RadixKeyLists

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Local variables as a list

In the proof of a procedure body the state is written out as ⟨frame [a, b, …], μ⟩: the list
holds the local variables 0, 1, …, and all further ones are 0.  An assignment to local x replaces
entry x of the list (setLocal).  The rules of this file treat one statement each.  They are told the
value that is assigned or stored, and they ask for one fact about each expression: that its
evaluation stays within the limits and gives this value (Expr.Gives).  This fact and the comparison
of the costs are proved by default from the hypotheses in the context.  Ends.forFrame and
Ends.forShape are the rules for counting loops in this form.  In the names of the rules, To says
that the state is ⟨frame l, μ⟩.

Locals by name, and locals whose values do not matter:

* `setLocals l [(x, a), (y, b), …]` is the list `l` after the assignments `x := a`, `y := b`, ….
  With the names of the locals for `x`, `y`, … it describes the locals of a procedure by name:
  `setLocals [] [(Size, n), (Bound, U), …]`.
* `updateLocals loc [(x, a), (y, b), …]` is the same for locals that are not given as a list.  A
  lemma about a piece of text that several procedures share is stated for arbitrary locals `loc`.
* `refreshLocals l loc xs` is the list `l` with the entries `xs` read from `loc`.
* `LocalsBut xs l loc` says that `loc` agrees with `frame l` except perhaps at the locals `xs`.  In
  an invariant, `xs` are the scratch variables.  `Ends.asFrame` goes from such locals to a list, and
  `LocalsBut.of_eq` comes back.
* `Ends.pieceTo` and `Ends.pieceToThen` use a lemma about a piece of text that assigns only the
  locals `xs`: afterwards the locals are `refreshLocals l loc' xs`, where `loc'` are the locals of
  which the lemma speaks.  The lemma need not mention the locals that the piece does not assign.
* `Ends.forScratch` is the rule for a counting loop whose body may change the scratch variables
  `xs`: the round says nothing about the locals.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## The list of the locals -/







/-- Zeros at the end of the list do not matter. -/
theorem frame_append_zeros (l : List ℤ) (n : ℕ) : _root_.Light.frame (l ++ List.replicate n 0) = _root_.Light.frame l := by
  funext y
  simp only [_root_.Light.frame, List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_replicate]
  split_ifs with h1 h2
  · rfl
  · rw [List.getElem?_eq_none (by omega)]
    rfl
  · rw [List.getElem?_eq_none (by omega)]

/-! ## The value of an expression -/



/-! ## One statement -/

section rules

variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}

















end rules

/-! ## Locals by name, and locals whose values do not matter -/























section
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}







/-! ## A piece of program text with a lemma of its own -/

variable {T T₁ : ℕ} {s s₁ s₂ : _root_.ThreeSum1960614.Machine.Light.Stmt} {Q R : _root_.ThreeSum1960614.Machine.Light.State → Prop}







/-! ## Counting loops with scratch variables -/



end

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
# Tables of powers

powTable(dst, L, b) writes 1, b, b², …, b^(L-1) into the L cells from dst and changes nothing else,
within `powTableTime L` steps (`powTable_meets`).  The list of these powers is `powList b L`.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



@[simp] theorem length_powList (b L : ℕ) : (_root_.Light.powList b L).length = L := by simp [_root_.Light.powList]

@[simp] theorem getElem_powList {b L j : ℕ} (h : j < (_root_.Light.powList b L).length) :
    (_root_.Light.powList b L)[j] = ((b ^ j : ℕ) : ℤ) := by
  simp [_root_.Light.powList]

namespace PowTable
open _root_.Light.PowTable








end PowTable

open _root_.Light.PowTable
open _root_.ThreeSum1960614.Machine.Light.PowTable











/-- **powTable(dst, L, b)** writes the powers 1, b, …, b^(L-1) into the L cells from dst and changes
nothing else. -/
theorem powTable_meets {p : ℕ} (hp : P[p]? = some _root_.ThreeSum1960614.Machine.Light.powTableBody) {μ : ℕ → ℤ} {dst L b : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + L ≤ lim.space)
    (hpow : ∀ j ≤ L, ((b ^ j : ℕ) : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [(dst : ℤ), L, b] μ (_root_.Light.powTableTime L) fun _ μ' =>
      _root_.ThreeSum1960614.Machine.Light.Seg μ' dst (_root_.Light.powList b L) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst L :=
  -- the local variables that are no arguments hold 0
  _root_.ThreeSum1960614.Machine.Light.Meets.of_body hp (_root_.ThreeSum1960614.Machine.Light.frame_append_zeros [(dst : ℤ), L, b] 2 ▸ _root_.ThreeSum1960614.Machine.Light.powTable_ends 0 0 [] hw hdst hpow)

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Machine evaluation of compact subset addresses

The current width decreases by one in each recursive call. Its highest
power of two is read from a table, so neither division nor a loop proportional
to the numeric bit-mask value occurs. Pascal coefficients are single reads
from the constructed rectangular table.
-/

namespace ThreeSum.LightSubsetAddress
open _root_.ThreeSum.LightSubsetAddress


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}



theorem powers_of_segment {μ : ℕ → ℤ} {base W : ℕ}
    (h : _root_.ThreeSum1960614.Machine.Light.Seg μ base (_root_.Light.powList 2 (W+1))) : _root_.ThreeSum.LightSubsetAddress.Powers μ base W := by
  intro i hi
  have hs := h i (by simp; omega)
  simpa only [_root_.ThreeSum1960614.Machine.Light.getElem_powList] using hs













end ThreeSum.LightSubsetAddress

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































theorem leftAt_eq_get {L h i : ℕ} (hi : i < L.choose h) :
    _root_.ThreeSum.ReportingHostPairEnumeration.leftAt L h i = (_root_.ThreeSum.ReportingHostPairEnumeration.lefts L h)[i]'(by simpa using hi) := by
  simp [_root_.ThreeSum.ReportingHostPairEnumeration.leftAt,List.getElem?_eq_getElem,hi]



theorem rightAt_eq_get {L h i j : ℕ} (hi : i < L.choose h) (hj : j < (L-h).choose h) :
    _root_.ThreeSum.ReportingHostPairEnumeration.rightAt L h i j = (_root_.ThreeSum.ReportingHostPairEnumeration.rights (_root_.ThreeSum.ReportingHostPairEnumeration.leftAt L h i) h)[j]'(by rw [_root_.ThreeSum.ReportingHostPairEnumeration.rights_length _ (_root_.ThreeSum.ReportingHostPairEnumeration.leftAt_card hi)]; exact hj) := by
  have hlen : j < (_root_.ThreeSum.ReportingHostPairEnumeration.rights (_root_.ThreeSum.ReportingHostPairEnumeration.leftAt L h i) h).length := by rw [_root_.ThreeSum.ReportingHostPairEnumeration.rights_length _ (_root_.ThreeSum.ReportingHostPairEnumeration.leftAt_card hi)]; exact hj
  simp [_root_.ThreeSum.ReportingHostPairEnumeration.rightAt,List.getElem?_eq_getElem hlen]







end ThreeSum.ReportingHostPairEnumeration

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # The constructed local pair arrays are aligned segments in one exact record order -/

namespace ThreeSum.ReportingHostPairSegments
open _root_.ThreeSum.ReportingHostPairSegments


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.ReportingHostPairEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration

set_option linter.unusedSimpArgs false

variable {α β : Type*}

theorem seg_flatMap_uniform {μ : ℕ → ℤ} {dst n : ℕ} (xs : List α) (f : α → List ℤ)
    (hlen : ∀ x ∈ xs, (f x).length = n)
    (hout : ∀ i (hi : i < xs.length), ∀ j (hj : j < n),
      μ (dst+i*n+j) = (f xs[i])[j]'(by rw [hlen _ (List.getElem_mem hi)]; exact hj)) :
    _root_.ThreeSum1960614.Machine.Light.Seg μ dst (xs.flatMap f) := by
  induction xs generalizing dst with
  | nil => simp [_root_.ThreeSum1960614.Machine.Light.Seg,_root_.ThreeSum1960614.Machine.Light.SegN]
  | cons x xs ih =>
    rw [List.flatMap_cons]
    apply platform_seg_append_e5df73c84b.mpr
    constructor
    · intro j hj
      have hn : j < n := by rw [← hlen x (by simp)]; exact hj
      have hh := hout 0 (by simp) j hn
      simp only [Nat.zero_mul,Nat.add_zero] at hh
      change μ (dst+j) = (f x)[j] at hh
      exact hh
    · rw [hlen x (by simp)]
      apply ih (by intro a ha; exact hlen a (by simp [ha]))
      intro i hi j hj
      have hh := hout (i+1) (by simpa using hi) j hj
      simpa only [List.getElem_cons_succ,Nat.add_mul,Nat.one_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
        using hh




@[simp] theorem leftMasks_length (L h : ℕ) : (_root_.ThreeSum.ReportingHostPairSegments.leftMasks L h).length = L.choose (2*h)*(2*h).choose h := by
  simp [_root_.ThreeSum.ReportingHostPairSegments.leftMasks,_root_.ThreeSum.ReportingHostPairEnumeration.pairs_length]

@[simp] theorem rightMasks_length (L h : ℕ) : (_root_.ThreeSum.ReportingHostPairSegments.rightMasks L h).length = L.choose (2*h)*(2*h).choose h := by
  simp [_root_.ThreeSum.ReportingHostPairSegments.rightMasks,_root_.ThreeSum.ReportingHostPairEnumeration.pairs_length]

theorem leftMasks_bounded (L h : ℕ) : ∀ x ∈ _root_.ThreeSum.ReportingHostPairSegments.leftMasks L h, |x| ≤ ((2^L : ℕ) : ℤ) := by
  intro x hx
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx
  rw [Int.abs_natCast]
  exact Int.ofNat_le.mpr (Nat.le_of_lt (_root_.ThreeSum.SubsetAddress.subsetMask_isMask p.1).1)

theorem rightMasks_bounded (L h : ℕ) : ∀ x ∈ _root_.ThreeSum.ReportingHostPairSegments.rightMasks L h, |x| ≤ ((2^L : ℕ) : ℤ) := by
  intro x hx
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx
  rw [Int.abs_natCast]
  exact Int.ofNat_le.mpr (Nat.le_of_lt (_root_.ThreeSum.SubsetAddress.subsetMask_isMask p.2).1)

theorem leftMasks_of_rows {μ : ℕ → ℤ} {L h dst : ℕ}
    (hout : ∀ i < L.choose h, ∀ j < (L-h).choose h,
      μ (dst+i*(L-h).choose h+j) = (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.ReportingHostPairEnumeration.leftAt L h i) : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Seg μ dst (_root_.ThreeSum.ReportingHostPairSegments.leftMasks L h) := by
  unfold _root_.ThreeSum.ReportingHostPairSegments.leftMasks _root_.ThreeSum.ReportingHostPairEnumeration.pairs
  rw [List.map_flatMap]
  simp only [List.map_map,Function.comp_def]
  apply _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairSegments.seg_flatMap_uniform (n := (L-h).choose h) (_root_.ThreeSum.ReportingHostPairEnumeration.lefts L h)
    (fun S => (_root_.ThreeSum.ReportingHostPairEnumeration.rights S h).map (fun _ => (_root_.ThreeSum.SubsetAddress.subsetMask S : ℤ)))
    (by intro S hS; simpa using _root_.ThreeSum.ReportingHostPairEnumeration.rights_length S ((_root_.ThreeSum.ReportingHostPairEnumeration.lefts_mem S).mp hS))
  intro i hi j hj
  have hin : i < L.choose h := by simpa using hi
  have hh := hout i hin j hj
  simpa only [List.getElem_map,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration.leftAt_eq_get hin] using hh

theorem rightMasks_of_rows {μ : ℕ → ℤ} {L h dst : ℕ}
    (hout : ∀ i < L.choose h, ∀ j < (L-h).choose h,
      μ (dst+i*(L-h).choose h+j) = (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.ReportingHostPairEnumeration.rightAt L h i j) : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Seg μ dst (_root_.ThreeSum.ReportingHostPairSegments.rightMasks L h) := by
  unfold _root_.ThreeSum.ReportingHostPairSegments.rightMasks _root_.ThreeSum.ReportingHostPairEnumeration.pairs
  rw [List.map_flatMap]
  simp only [List.map_map,Function.comp_def]
  apply _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairSegments.seg_flatMap_uniform (n := (L-h).choose h) (_root_.ThreeSum.ReportingHostPairEnumeration.lefts L h)
    (fun S => (_root_.ThreeSum.ReportingHostPairEnumeration.rights S h).map (fun R => (_root_.ThreeSum.SubsetAddress.subsetMask R : ℤ)))
    (by intro S hS; simpa using _root_.ThreeSum.ReportingHostPairEnumeration.rights_length S ((_root_.ThreeSum.ReportingHostPairEnumeration.lefts_mem S).mp hS))
  intro i hi j hj
  have hin : i < L.choose h := by simpa using hi
  have hh := hout i hin j hj
  simpa only [List.getElem_map,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration.rightAt_eq_get hin hj,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration.leftAt_eq_get hin] using hh

theorem program_meets {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ → ℤ} {L h srcS dstL dstR work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hh : 2*h ≤ L)
    (hS : srcS+L.choose h ≤ dstL)
    (hL : dstL+L.choose h*(L-h).choose h ≤ dstR)
    (hR : dstR+L.choose h*(L-h).choose h ≤ work)
    (hspace : work+2*L+2 ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+L+3 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPairRows.program 7 d [L,h,srcS,dstL,dstR,work]
      μ (_root_.ThreeSum.LightReportingPairRows.time L h)
      (fun r μ' => r = (L.choose (2*h)*(2*h).choose h : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.Seg μ' dstL (_root_.ThreeSum.ReportingHostPairSegments.leftMasks L h) ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ' dstR (_root_.ThreeSum.ReportingHostPairSegments.rightMasks L h) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ μ' srcS) := by
  apply (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPairRows.program_meets hw hh hS hL hR hspace hword hd).mono le_rfl
  rintro r μ' ⟨hr,_,hout,hkeep⟩
  exact ⟨hr,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairSegments.leftMasks_of_rows (by intro i hi j hj; exact (hout i hi j hj).1),
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairSegments.rightMasks_of_rows (by intro i hi j hj; exact (hout i hi j hj).2),hkeep⟩

end ThreeSum.ReportingHostPairSegments

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightReportingPrefixArrays
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixArrays

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.ReportingHostPairEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration
open _root_.ThreeSum.ReportingHostPairSegments
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairSegments
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixArrays.program_meets__implementation_b4f6c1e63c {μ : ℕ → ℤ} {L h k srcS pairL pairR stageL stageR work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hh : 2*h ≤ L)
    (hS : srcS+L.choose h ≤ pairL)
    (hL : pairL+_root_.ThreeSum.LightReportingPrefixArrays.localCount L h ≤ pairR) (hR : pairR+_root_.ThreeSum.LightReportingPrefixArrays.localCount L h ≤ stageL)
    (hstageL : _root_.ThreeSum.LightRadixKeys.space stageL (_root_.ThreeSum.LightReportingPrefixArrays.localCount L h) k ≤ stageR)
    (hstageR : _root_.ThreeSum.LightRadixKeys.space stageR (_root_.ThreeSum.LightReportingPrefixArrays.localCount L h) k ≤ work)
    (hspace : work+2*L+2 ≤ lim.space)
    (hpowWord : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hkeysWord : (_root_.ThreeSum.LightRadixKeys.word (2^L) (2^L) k : ℤ) ≤ lim.word)
    (hd : d+L+k+4 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixArrays.program 10 d [L,h,k,srcS,pairL,pairR,stageL,stageR,work] μ (_root_.ThreeSum.LightReportingPrefixArrays.time L h k)
      (fun r μ' =>
        r = (stageL+_root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum.LightReportingPrefixArrays.localCount L h) k : ℕ) ∧
        μ' (stageL+_root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum.LightReportingPrefixArrays.localCount L h) k) = ((_root_.ThreeSum.LightReportingPrefixArrays.localCount L h)^k : ℕ) ∧
        μ' (stageR+_root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum.LightReportingPrefixArrays.localCount L h) k) = ((_root_.ThreeSum.LightReportingPrefixArrays.localCount L h)^k : ℕ) ∧
        _root_.ThreeSum1960614.Machine.Light.Seg μ' (stageL+_root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum.LightReportingPrefixArrays.localCount L h) k+1)
          (_root_.ThreeSum.RadixKeyLists.values ((2^L : ℕ) : ℤ) (_root_.ThreeSum.ReportingHostPairSegments.leftMasks L h) k) ∧
        _root_.ThreeSum1960614.Machine.Light.Seg μ' (stageR+_root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum.LightReportingPrefixArrays.localCount L h) k+1)
          (_root_.ThreeSum.RadixKeyLists.values ((2^L : ℕ) : ℤ) (_root_.ThreeSum.ReportingHostPairSegments.rightMasks L h) k) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ μ' srcS) := by
  have hpos : 0 < _root_.ThreeSum.LightReportingPrefixArrays.localCount L h := Nat.mul_pos (Nat.choose_pos hh) (Nat.choose_pos (by omega))
  have hleftLen : (_root_.ThreeSum.ReportingHostPairSegments.leftMasks L h).length = _root_.ThreeSum.LightReportingPrefixArrays.localCount L h := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairSegments.leftMasks_length L h
  have hrightLen : (_root_.ThreeSum.ReportingHostPairSegments.rightMasks L h).length = _root_.ThreeSum.LightReportingPrefixArrays.localCount L h := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairSegments.rightMasks_length L h
  have hstageOrder : stageL ≤ stageR := by unfold _root_.ThreeSum.LightRadixKeys.space at hstageL; omega
  have hworkOrder : stageR ≤ work := by unfold _root_.ThreeSum.LightRadixKeys.space at hstageR; omega
  have hpowBound : ∀ j ≤ L+1, ((2^j : ℕ) : ℤ) ≤ lim.word := by
    intro j hj
    exact (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) hj)).trans hpowWord
  have hpairProd : L.choose h*(L-h).choose h = _root_.ThreeSum.LightReportingPrefixArrays.localCount L h := _root_.ThreeSum1960614.Machine.ThreeSum.LayerCounts.vertex_degree_identity L h
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 10) (by rfl : program[10]? = some (body 7 2 8))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixArrays.body _root_.ThreeSum.LightReportingPrefixArrays.time
  have hp := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairSegments.program_meets (d := d+1) (μ := μ)
    (L := L) (h := h) (srcS := srcS) (dstL := pairL) (dstR := pairR) (work := work)
    hw hh hS (by simpa only [hpairProd] using hL) (by rw [hpairProd]; omega) hspace hpowWord (by omega)).append
      [_root_.ThreeSum1960614.Machine.ThreeSum.LightRadixKeys.body 8 9,_root_.ThreeSum1960614.Machine.ThreeSum.LightRadixRows.body 6,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixArrays.body 7 2 8]
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
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingPairRows.time, _root_.ThreeSum.LightRadixKeys.time, _root_.Light.powTableTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightReportingPairRows.time, _root_.ThreeSum.LightRadixKeys.time, _root_.Light.powTableTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightReportingPairRows.time, _root_.ThreeSum.LightRadixKeys.time, _root_.Light.powTableTime] <;> omega)
     on_goal -1 => (rintro count μ₁ ⟨hcount, hleft, hright, hkeepPair⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hcount' : count = (_root_.ThreeSum.LightReportingPrefixArrays.localCount L h : ℤ) := hcount
  have hpow := _root_.ThreeSum1960614.Machine.Light.powTable_meets (P := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixArrays.program) (p := 2) (d := d+1) (μ := μ₁)
    (dst := work) (L := L+1) (b := 2) rfl hw (by omega) hpowBound
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hpow _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hpow ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingPairRows.time, _root_.ThreeSum.LightRadixKeys.time, _root_.Light.powTableTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightReportingPairRows.time, _root_.ThreeSum.LightRadixKeys.time, _root_.Light.powTableTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightReportingPairRows.time, _root_.ThreeSum.LightRadixKeys.time, _root_.Light.powTableTime] <;> omega)
     on_goal -1 => (rintro powRet μ₂ ⟨hpowers, hkeepPowers⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hreadPow := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress.powers_of_segment hpowers L le_rfl
  have hreadPowNat : μ₂ (work+L) = ((2^L : ℕ) : ℤ) := by simpa using hreadPow
  have hradix := hpowBound L (by omega)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (2 ^ L : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadPow, hreadPowNat, _root_.ThreeSum.LightReportingPairRows.time, _root_.ThreeSum.LightRadixKeys.time, _root_.Light.powTableTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hreadPow, hreadPowNat, _root_.ThreeSum.LightReportingPairRows.time, _root_.ThreeSum.LightRadixKeys.time, _root_.Light.powTableTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadPow, hreadPowNat, _root_.ThreeSum.LightReportingPairRows.time, _root_.ThreeSum.LightRadixKeys.time, _root_.Light.powTableTime] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hleft₂ : _root_.ThreeSum1960614.Machine.Light.Seg μ₂ pairL (_root_.ThreeSum.ReportingHostPairSegments.leftMasks L h) := by
    intro i hi
    rw [hkeepPowers _ (Or.inl (by rw [hleftLen] at hi; omega))]
    exact hleft i hi
  have hright₂ : _root_.ThreeSum1960614.Machine.Light.Seg μ₂ pairR (_root_.ThreeSum.ReportingHostPairSegments.rightMasks L h) := by
    intro i hi
    rw [hkeepPowers _ (Or.inl (by rw [hrightLen] at hi; omega))]
    exact hright i hi
  have hl := _root_.ThreeSum1960614.Machine.ThreeSum.LightRadixKeys.meets (P := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixArrays.program) (pMain := 8) (pRows := 9) (pAffine := 6)
    (src := pairL) (dst := stageL) (p := 2^L) (U := 2^L) rfl rfl rfl
    (_root_.ThreeSum.ReportingHostPairSegments.leftMasks L h) hw (by rw [hleftLen]; omega) (by rw [hleftLen]; exact hpos)
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairSegments.leftMasks_bounded L h) k (d+1) μ₂
    (by rw [hleftLen]; exact hstageL.trans (by omega)) hkeysWord (by omega) hleft₂
  simp only [hleftLen] at hl
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
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcount', _root_.ThreeSum.LightReportingPairRows.time, _root_.ThreeSum.LightRadixKeys.time, _root_.Light.powTableTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hcount', _root_.ThreeSum.LightReportingPairRows.time, _root_.ThreeSum.LightRadixKeys.time, _root_.Light.powTableTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcount', _root_.ThreeSum.LightReportingPairRows.time, _root_.ThreeSum.LightRadixKeys.time, _root_.Light.powTableTime] <;> omega)
     on_goal -1 => (rintro leftHead μ₃ ⟨hleftHead, hleftHeader, hleftArray, hkeepLeft⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hright₃ : _root_.ThreeSum1960614.Machine.Light.Seg μ₃ pairR (_root_.ThreeSum.ReportingHostPairSegments.rightMasks L h) := by
    intro i hi
    rw [hkeepLeft _ (by rw [hrightLen] at hi; omega)]
    exact hright₂ i hi
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.LightRadixKeys.meets (P := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixArrays.program) (pMain := 8) (pRows := 9) (pAffine := 6)
    (src := pairR) (dst := stageR) (p := 2^L) (U := 2^L) rfl rfl rfl
    (_root_.ThreeSum.ReportingHostPairSegments.rightMasks L h) hw (by rw [hrightLen]; omega) (by rw [hrightLen]; exact hpos)
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairSegments.rightMasks_bounded L h) k (d+1) μ₃
    (by rw [hrightLen]; exact hstageR.trans (by omega)) hkeysWord (by omega) hright₃
  simp only [hrightLen] at hr
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
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcount', _root_.ThreeSum.LightReportingPairRows.time, _root_.ThreeSum.LightRadixKeys.time, _root_.Light.powTableTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hcount', _root_.ThreeSum.LightReportingPairRows.time, _root_.ThreeSum.LightRadixKeys.time, _root_.Light.powTableTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcount', _root_.ThreeSum.LightReportingPairRows.time, _root_.ThreeSum.LightRadixKeys.time, _root_.Light.powTableTime] <;> omega)
     on_goal -1 => (rintro rightHead μ₄ ⟨hrightHead, hrightHeader, hrightArray, hkeepRight⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hleftBound : stageL+_root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum.LightReportingPrefixArrays.localCount L h) k+1+(_root_.ThreeSum.LightReportingPrefixArrays.localCount L h)^k ≤ stageR := hstageL
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (stageL + _root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum.LightReportingPrefixArrays.localCount L h) k : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hleftHead, _root_.ThreeSum.LightReportingPairRows.time, _root_.ThreeSum.LightRadixKeys.time, _root_.Light.powTableTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hleftHead, _root_.ThreeSum.LightReportingPairRows.time, _root_.ThreeSum.LightRadixKeys.time, _root_.Light.powTableTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hleftHead, _root_.ThreeSum.LightReportingPairRows.time, _root_.ThreeSum.LightRadixKeys.time, _root_.Light.powTableTime] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  refine ⟨by simp,?_,hrightHeader,?_,hrightArray,?_⟩
  · change μ₄ (stageL+_root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum.LightReportingPrefixArrays.localCount L h) k) = _
    rw [hkeepRight _ (by omega)]
    exact hleftHeader
  · intro i hi
    change μ₄ (stageL+_root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum.LightReportingPrefixArrays.localCount L h) k+1+i) = _
    rw [hkeepRight _ (by simp only [_root_.ThreeSum1960614.Machine.ThreeSum.RadixKeyLists.values_length,hleftLen] at hi; omega)]
    exact hleftArray i hi
  · intro i hi
    exact (hkeepRight i (by omega)).trans ((hkeepLeft i (by omega)).trans
      ((hkeepPowers i (Or.inl (by omega))).trans (hkeepPair i hi)))
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixArrays.program_meets__implementation_b4f6c1e63c) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixArrays.program_meets__implementation_b4f6c1e63c)

#print axioms solution
