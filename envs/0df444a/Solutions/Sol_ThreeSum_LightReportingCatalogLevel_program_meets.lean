-- Prove2me | solution 1 for ThreeSum.LightReportingCatalogLevel.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T17:19:38.952372+00:00
-- url     : https://prove2.me/submissions/d7243454-d095-4372-97c2-fc2fe247ce24

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
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
import Mathlib.Algebra.Order.Field.Basic
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
import Mathlib.Data.Int.Cast.Lemmas
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
import Mathlib.Data.Nat.Cast.Order.Ring
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
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_LightReportingCatalogBatch_program_meets
import Theorems.Thm_ThreeSum_LightReportingFilter_meets
import Theorems.Thm_ThreeSum_ReportingHostSuffixValueBounds_prefix_count_le_word


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostPrefixOrder
end ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSumApsp
end ThreeSumApsp

section


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

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Runs -/

/-- A procedure of a program is a procedure, with the same number, of the program with more
procedures appended. -/
theorem getElem?_append_of_eq_some {P : Program} {p : ℕ} {body : Stmt} (h : P[p]? = some body)
    (R : Program) : (P ++ R)[p]? = some body := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h














/-- A run stays a run when procedures are appended to the program. -/
theorem Exec.append {s : Stmt} {σ σ' : State} {c : ℕ} (h : Exec lim P d s σ σ' c) (R : Program) :
    Exec lim (P ++ R) d s σ σ' c := by
  induction h with
  | skip => exact .skip
  | set h => exact .set h
  | store h₁ h₂ h₃ => exact .store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact .iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact .iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact .whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact .whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact .call h₁ (getElem?_append_of_eq_some h₂ R) h₃ ih

/-! ## The rules -/






/-- More time and a weaker conclusion. -/
theorem Ends.mono {s σ T T' Q Q'} (h : Ends lim P d s σ T Q) (hT : T ≤ T')
    (hQ : ∀ σ', Q σ' → Q' σ') : Ends lim P d s σ T' Q' := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he, hc.trans hT, hQ _ hq⟩

/-- What is proved about a program holds for the program with more procedures appended. -/
theorem Ends.append {s σ T Q} (h : Ends lim P d s σ T Q) (R : Program) :
    Ends lim (P ++ R) d s σ T Q := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he.append R, hc, hq⟩

theorem Ends.skip {σ T} {Q : State → Prop} (h : Q σ) : Ends lim P d .skip σ T Q :=
  ⟨σ, 0, .skip, Nat.zero_le _, h⟩











theorem Ends.seq {σ T s₁ s₂} {Q : State → Prop} (T₁ T₂ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' T₂ Q) (hT : T₁ + T₂ ≤ T) :
    Ends lim P d (.seq s₁ s₂) σ T Q := by
  obtain ⟨σ', c₁, he₁, hc₁, σ'', c₂, he₂, hc₂, hq⟩ := h
  exact ⟨σ'', _, .seq he₁ he₂, by omega, hq⟩

























































































/-- Calls: verify the body from the frame made of the arguments. -/
theorem Ends.call {σ T p args x body} {Q : State → Prop} (T' : ℕ) (ha : ∀ e ∈ args, e.Safe lim σ)
    (hp : P[p]? = some body) (hd : d < lim.depth)
    (h : Ends lim P (d + 1) body ⟨frame (args.map (·.val σ)), σ.mem⟩ T'
      fun σ' => Q ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T) : Ends lim P d (.call p args x) σ T Q := by
  obtain ⟨σ', k, he, hk, hq⟩ := h
  exact ⟨_, _, .call ha hp hd he, by omega, hq⟩

/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/




























/-! ## Simplification -/

attribute [simp] Expr.val Expr.cost Expr.Safe Op.eval Cond.Holds Cond.cost Cond.Safe frame
















/-! ## The limits -/
























end Light

end
end

section


/-!
# Derived rules: time that is not typed, blocks, counting loops

The rules of this file spare the typing of step counts.  Ends.next gives the first statement its
time and the rest of the program what is left; Ends.setThen, Ends.storeThen and Ends.iteThen do the
same for one assignment, store or branch, and Ends.setLast, Ends.storeLast and Ends.iteLast treat
the last statement of a program.  `Ends.pieceThen` and `Ends.pieceLast` are the two forms for a
piece of the program that has a lemma of its own.  In every rule the main premises come first, then
the side conditions, and last the comparison of times.  The comparison has the default proof
`light_time`, safety conditions have the default proof `light_side`.

A block is a statement without loops and calls.  s.Runs lim σ R says that the block s runs safely
from σ and ends in a state that satisfies R; Ends.block turns this into a fact about time, with the
cost computed. Ends.whileBlock is the rule for a loop whose body is a block.

Stmt.for i hi body is the loop "for i = 0, …, hi - 1 do body".  The rule Ends.for owns the counter:
the safety of the test and of the increment and the number of steps of the loop are settled here,
once. Ends.forMem is the common case in which the body changes no local variable, so that the
invariant speaks about the memory only.  The three parts of every loop rule are called start, round
and done.  A loop rule is told a bound b on the steps of a round; for a round that is a block with
a name, say xRound, this is xRound.blockCost.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Blocks -/




































/-! ## The default proofs -/



































/-! ## Rules for blocks -/















































/-! ## Sequencing: what is left of the time goes to the rest of the program -/

/-- The first statement gets T₁ steps, the rest of the program what is left of T. -/
theorem Ends.next {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop} (T₁ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' (T - T₁) Q)
    (hT : T₁ ≤ T := by first
                           |
                             ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                   List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                               (first
                                 | omega
                                 | ((ring_nf); (omega))))
                           | omega
                           |
                             (simp [] <;>
                                 first
                                 | omega
                                 | ((ring_nf); (omega)))) : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q :=
  Ends.seq T₁ (T - T₁) h (by omega)

/-- Brackets do not matter: a piece of several statements, followed by the rest of the program, is
run statement by statement. -/
theorem Ends.seqAssoc {σ : State} {T : ℕ} {s₁ s₂ s₃ : Stmt} {Q : State → Prop}
    (h : Ends lim P d ((Light.Stmt.seq s₁ (Light.Stmt.seq s₂ s₃))) σ T Q) : Ends lim P d ((Light.Stmt.seq (Light.Stmt.seq s₁ s₂) s₃)) σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂₃ =>
    cases he₂₃ with
    | seq he₂ he₃ => exact ⟨σ', _, .seq (.seq he₁ he₂) he₃, by omega, hq⟩

/-- A `skip` before the rest of the program takes no step. -/
theorem Ends.skipThen {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop} (h : Ends lim P d s σ T Q) :
    Ends lim P d ((Light.Stmt.seq .skip s)) σ T Q :=
  Ends.seq 0 T (Ends.skip h) (by omega)

/-- A `skip` may be put behind a statement. -/
theorem Ends.skipLast {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop}
    (h : Ends lim P d ((Light.Stmt.seq s .skip)) σ T Q) : Ends lim P d s σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂ =>
    cases he₂
    exact ⟨σ', _, he₁, by omega, hq⟩

/-- A program that is defined as a sequence may be treated as the sequence. -/
theorem Ends.seqSelf {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q) : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q :=
  h












































































/-! ## Loops whose body is a block -/














/-! ## Counting loops -/











































































end Light

end
end

section


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

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The list of the locals -/









/-- Reading a local after an assignment. -/
theorem frame_setLocal : ∀ (l : List ℤ) (x : ℕ) (z : ℤ) (y : ℕ),
    frame (setLocal l x z) y = if y = x then z else frame l y
  | [], 0, z, 0 => by simp
  | [], 0, z, y + 1 => by simp
  | [], x + 1, z, 0 => by simp
  | [], x + 1, z, y + 1 => by simpa using frame_setLocal [] x z y
  | a :: l, 0, z, 0 => by simp
  | a :: l, 0, z, y + 1 => by simp
  | a :: l, x + 1, z, 0 => by simp
  | a :: l, x + 1, z, y + 1 => by simpa using frame_setLocal l x z y

/-- An assignment to a local, in terms of the list. -/
theorem update_frame_setLocal (l : List ℤ) (x : ℕ) (z : ℤ) :
    Function.update (frame l) x z = frame (setLocal l x z) := by
  funext y
  rw [frame_setLocal, Function.update_apply]











/-! ## The value of an expression -/





/-! ## One statement -/

section rules

variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : State → Prop}


















































































































end rules

/-! ## Locals by name, and locals whose values do not matter -/




































































section
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}

























/-! ## A piece of program text with a lemma of its own -/

variable {T T₁ : ℕ} {s s₁ s₂ : Stmt} {Q R : State → Prop}































/-! ## Counting loops with scratch variables -/













































end

end Light

end
end

section


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

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Specifications of procedures -/







section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}

/-- From a theorem about a body to the specification. -/
theorem Meets.of_body {args : List ℤ} {Q : ℤ → (ℕ → ℤ) → Prop} {body : Stmt}
    (hp : P[p]? = some body)
    (h : Ends lim P d body ⟨frame args, μ⟩ T fun σ' => Q (σ'.loc 0) σ'.mem) :
    Meets lim P p d args μ T Q :=
  ⟨body, hp, h⟩

















/-- A specification holds for the program with more procedures appended. -/
theorem Meets.append (h : Meets lim P p d vals μ T R) (P' : Program) :
    Meets lim (P ++ P') p d vals μ T R := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, getElem?_append_of_eq_some hp P', he.append P'⟩

end

/-! ## The rule for calls -/

section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : State → Prop} {s : Stmt}

/-- `x := p(args)`, where the arguments give vals.  The procedure runs at depth d + 1. -/
theorem Ends.callLast (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Q ⟨Function.update loc x r, μ'⟩)
    (ha : (∀ e ∈ args, e.Safe lim ⟨loc, μ⟩) ∧ args.map (·.val ⟨loc, μ⟩) = vals := by (((try have := Light.Std.space_le (by assumption)));
                                                                                                        ((try have := Light.Std.const_le (by assumption)));
                                                                                                        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
                                                        |
                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                            (first
                                                              | omega
                                                              | ((ring_nf); (omega))))
                                                        | omega
                                                        |
                                                          (simp [] <;>
                                                              first
                                                              | omega
                                                              | ((ring_nf); (omega)))) :
    Ends lim P d (.call p args x) ⟨loc, μ⟩ T Q := by
  obtain ⟨body, hb, he⟩ := hp
  obtain ⟨hs, rfl⟩ := ha
  exact Ends.call T' hs hb hd (he.mono le_rfl fun _ hR => h _ _ hR) hT











/-- `x := p(args)`, with the local variables as a list.  The procedure runs at depth d + 1. -/
theorem Ends.callTo (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Q ⟨frame (setLocal l x r), μ'⟩)
    (ha : (∀ e ∈ args, e.Safe lim ⟨frame l, μ⟩) ∧ args.map (·.val ⟨frame l, μ⟩) = vals := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
                                                        |
                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                            (first
                                                              | omega
                                                              | ((ring_nf); (omega))))
                                                        | omega
                                                        |
                                                          (simp [] <;>
                                                              first
                                                              | omega
                                                              | ((ring_nf); (omega)))) :
    Ends lim P d (.call p args x) ⟨frame l, μ⟩ T Q :=
  Ends.callLast hp (fun r μ' hR => update_frame_setLocal l x r ▸ h r μ' hR) ha hd hT

/-- `x := p(args) ; s`, with the local variables as a list.  The procedure runs at depth d + 1. -/
theorem Ends.callToThen (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Ends lim P d s ⟨frame (setLocal l x r), μ'⟩
      (T - ((args.map Expr.cost).sum + 2 + T')) Q)
    (ha : (∀ e ∈ args, e.Safe lim ⟨frame l, μ⟩) ∧ args.map (·.val ⟨frame l, μ⟩) = vals := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
                                                        |
                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                            (first
                                                              | omega
                                                              | ((ring_nf); (omega))))
                                                        | omega
                                                        |
                                                          (simp [] <;>
                                                              first
                                                              | omega
                                                              | ((ring_nf); (omega)))) :
    Ends lim P d ((Light.Stmt.seq (.call p args x) s)) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.callTo hp h ha hd le_rfl) hT

end

end Light

end
end

section


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

open ThreeSumApsp







variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}































































/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]

















































/-- A segment that does not meet the region is kept. -/
theorem Seg.of_sameOutside (h : Seg μ b l) (hs : SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : Seg μ' b l :=
  h.congr fun i hi => hs _ (by omega)









/-- Reading a cell of a segment of natural numbers, with the proof that the index is in range. -/
theorem SegN.getElem {l : List ℕ} (h : SegN μ a l) {i : ℕ} (hi : i < l.length) :
    μ (a + i) = (l[i] : ℕ) := by
  rw [h i (by simpa using hi), List.getElem_map]






















/-- A segment of natural numbers that does not meet the region is kept. -/
theorem SegN.of_sameOutside {l : List ℕ} (h : SegN μ b l) (hs : SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : SegN μ' b l :=
  Seg.of_sameOutside h hs (by simpa using hd)





































end Light

end
end

section


/-! # Actual shared-catalog queries followed by stable positive compaction -/

namespace ThreeSum.LightReportingCatalogLevel

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]











theorem program_meets_sourceProof
    {μ : ℕ → ℤ} {h J k t baseL baseR boxCut boxBase indexBase ptrBase inL inR n dst selected maskBase work depth : ℕ}
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (pres : ℕ → List (Finset (Fin (512*h)))) (hk : k ≤ J)
    (hp : ∀ i < n, ValidPrefix w.2.2 k (pres i))
    (hkey : w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1 % pMod+lift w.2.1*pMod+shift)-globalKey w.2.2)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdataL : baseL+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ dst)
    (hdataR : baseR+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ dst)
    (hindex : indexBase+count h k ≤ dst) (hptr : ptrBase+count h k ≤ dst)
    (hboxesEnd : boxBase+count h k*stride (suffixStage J (512*h) k) boxCut ≤ dst)
    (hinL : inL+n ≤ dst) (hinR : inR+n ≤ dst)
    (hdst : dst+n ≤ selected) (hselected : selected+n ≤ maskBase)
    (hmasks : maskBase+LightSparseQuery.queryItems (residualSize h J k) t ≤ work)
    (hspace : work+1+tableSize (width h J)+(width h J+1) ≤ lim.space)
    (hpowSpace : work+(2*width h J+2) ≤ lim.space)
    (hemodSpace : work+(Nat.log 2 (LightReportingCatalogLookup.valueBound (width h J) (count h k)+1)+2) ≤ lim.space)
    (hword : (((width h J+1)*2^(width h J+1) : ℕ) : ℤ) ≤ lim.word)
    (hlookupWord : (LightReportingCatalogLookup.word (width h J) (count h k) : ℤ) ≤ lim.word)
    (hvalueWord : (LightSparseQuery.magnitudeBound (suffixStage J (512*h) k) (suffixStage J (512*h) k)
      (residualSize h J k) t B.card C.card : ℤ) ≤ lim.word)
    (ht : t ≤ residualSize h J k+1) (hboxCut : boxCut ≤ residualSize h J k)
    (hflags : residualSize h J k-t ≤ boxCut)
    (hstoredL : LightZetaStages.StoredThrough μ baseL (sourceCut h J)
      (leftSource pMod B b w.2.2) (width h J))
    (hstoredR : LightZetaStages.StoredThrough μ baseR (sourceCut h J)
      (rightSource pMod shift C c w.2.2) (width h J))
    (hindexData : ∃ S : List ℤ, Seg μ indexBase S ∧
      S.Perm (ReportingHostPackedCatalog.codes (ReportingHostPackedCatalog.prefixKey h J k) (count h k)) ∧
      S.Pairwise (· ≤ ·))
    (hptrs : SegN μ ptrBase (List.ofFn fun i : Fin (count h k) =>
      boxBase+i.val*stride (suffixStage J (512*h) k) boxCut))
    (hboxes : ∀ i < count h k, LightBoxStages.StoredThrough μ
      (boxBase+i*stride (suffixStage J (512*h) k) boxCut) boxCut
      (leafWeight (block_fit hk) (leftSource pMod B b w.2.2) (rightSource pMod shift C c w.2.2)
        (suffixStage J (512*h) k) (preL h J k i) (preR h J k i))
      (suffixStage J (512*h) k))
    (hreadL : ∀ i < n, μ (inL+i) = (subsetMask (leftPrefix k (prefixRows (J := J) (pres i))) : ℤ))
    (hreadR : ∀ i < n, μ (inR+i) =
      (subsetMask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) (pres i))) : ℤ))
    (hd : depth+2*width h J+14 ≤ lim.depth) :
    Meets lim program 38 depth
      [width h J,sourceCut h J,suffixStage J (512*h) k,k*h,k*h,
        suffixStage J (512*h) k,k*(512*h),residualSize h J k,subsetMask (querySet k (outputRows w.2.2)),
        t,baseL,baseR,boxCut,indexBase,ptrBase,count h k,inL,inR,n,dst,maskBase,work,selected]
      μ (time h J k t n)
      (fun r μ' =>
        let counts := fun i => prefixQuery (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k (pres i)
        r = ((LightReportingFilter.selected counts n).length : ℤ) ∧
        SegN μ' selected (LightReportingFilter.selected counts n) ∧
        SegN μ' dst (List.ofFn fun i : Fin n => counts i.val) ∧ Kept μ μ' dst) := by
  let counts := fun i => prefixQuery (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k (pres i)
  have hcountWord (i : ℕ) (hi : i < n) : (counts i : ℤ) ≤ lim.word :=
    ReportingHostSuffixValueBounds.prefix_count_le_word pMod shift A B C a b c w (pres i)
      hk (hp i hi) hkey hvalueWord
  apply Meets.of_body (p := 38) (by rfl : program[38]? = some (body 36 37))
  unfold body time
  have hb := (LightReportingCatalogBatch.program_meets (depth := depth+1) (μ := μ)
    (inL := inL) (inR := inR) (n := n) (dst := dst) (maskBase := maskBase) (work := work)
    pMod shift A B C a b c w pres hk hp hkey hw hdataL hdataR hindex hptr hboxesEnd
    hinL hinR (by omega) hmasks hspace hpowSpace hemodSpace hword hlookupWord hvalueWord
    ht hboxCut hflags hstoredL hstoredR hindexData hptrs hboxes hreadL hreadR (by omega)).append suffix
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      | refine Light.Ends.callToThen (hb _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hb ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightReportingCatalogBatch.time, LightReportingFilter.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightReportingCatalogBatch.time, LightReportingFilter.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul,
                LightReportingCatalogBatch.time, LightReportingFilter.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro ret μ₁ ⟨hcounts, hkeepBatch⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hreads (i : ℕ) (hi : i < n) : μ₁ (dst+i) = (counts i : ℤ) := by
    have hs := hcounts.getElem (i := i) (by simpa only [List.length_ofFn] using hi)
    simpa only [List.getElem_ofFn] using hs
  have hf := LightReportingFilter.meets (P := program) (p := 37) (d := depth+1)
    (μ := μ₁) (src := dst) (dst := selected) (n := n) counts rfl hw (by omega) (by omega)
    (Or.inl hdst) hcountWord hreads
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      | refine Light.Ends.callToThen (hf _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hf ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightReportingCatalogBatch.time, LightReportingFilter.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightReportingCatalogBatch.time, LightReportingFilter.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul,
                LightReportingCatalogBatch.time, LightReportingFilter.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro found μ₂ ⟨hfound, hselectedOut, hkeepFilter⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  refine ⟨hfound,hselectedOut,?_,?_⟩
  · exact hcounts.of_sameOutside hkeepFilter (Or.inl (by simpa using hdst))
  · intro i hi
    exact (hkeepFilter i (Or.inl (by omega))).trans (hkeepBatch i ⟨by omega,Or.inl hi⟩)










end ThreeSum.LightReportingCatalogLevel

end

universe u_1 u_2 u_3

theorem solution : ∀ {lim : Light.Limits} {α : Type u_1} {β : Type u_2} {γ : Type u_3} [Fintype.{u_1} α] [Fintype.{u_2} β]
  [Fintype.{u_3} γ] [inst : DecidableEq.{u_1 + 1} α] [DecidableEq.{u_2 + 1} β] [DecidableEq.{u_3 + 1} γ] {μ : Nat → Int}
  {h J k t baseL baseR boxCut boxBase indexBase ptrBase inL inR n dst selected maskBase work depth : Nat}
  (pMod shift : Int) (A : Finset.{u_1} α) (B : Finset.{u_2} β) (C : Finset.{u_3} γ) (a : α → Int) (b : β → Int)
  (c : γ → Int) (w : ThreeSum.RawReporting.Wanted.{u_1} h J α)
  (pres :
    Nat →
      List.{0}
        (Finset.{0}
          (Fin
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
  (hk : @LE.le.{0} Nat instLENat k J)
  (hp :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @ThreeSum.StoredReporting.ValidPrefix h J
          (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (ThreeSum.GlobalEncoding.GlobalOutput h J)
            (@Prod.snd.{u_1, 0} α
              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput h J))
              w))
          k (pres i))
  (hkey :
    And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) A
        (@Prod.fst.{u_1, 0} α
          (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (ThreeSum.GlobalEncoding.GlobalOutput h J))
          w))
      (@Dvd.dvd.{0} Int Int.instDvd (ThreeSum.GlobalEncoding.globalModulus h J)
        (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
              (@HMod.hMod.{0, 0, 0} Int Int Int (@instHMod.{0} Int Int.instMod)
                (a
                  (@Prod.fst.{u_1, 0} α
                    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (ThreeSum.GlobalEncoding.GlobalOutput h J))
                    w))
                pMod)
              (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                (ThreeSum.RawIncidences.lift
                  (@Prod.fst.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (ThreeSum.GlobalEncoding.GlobalOutput h J)
                    (@Prod.snd.{u_1, 0} α
                      (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (ThreeSum.GlobalEncoding.GlobalOutput h J))
                      w)))
                pMod))
            shift)
          (@ThreeSum.GlobalEncoding.globalKey h J
            (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (ThreeSum.GlobalEncoding.GlobalOutput h J)
              (@Prod.snd.{u_1, 0} α
                (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (ThreeSum.GlobalEncoding.GlobalOutput h J))
                w))))))
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hdataL :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) baseL
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.LightBlockQuery.width h J)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (ThreeSum.SubsetAddress.downsetCap (ThreeSum.LightBlockQuery.width h J)
            (ThreeSum.LightBlockQuery.sourceCut h J))))
      dst)
  (hdataR :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) baseR
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.LightBlockQuery.width h J)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (ThreeSum.SubsetAddress.downsetCap (ThreeSum.LightBlockQuery.width h J)
            (ThreeSum.LightBlockQuery.sourceCut h J))))
      dst)
  (hindex :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) indexBase
        (ThreeSum.LightReportingPrefixCatalog.count h k))
      dst)
  (hptr :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ptrBase
        (ThreeSum.LightReportingPrefixCatalog.count h k))
      dst)
  (hboxesEnd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) boxBase
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (ThreeSum.LightReportingPrefixCatalog.count h k)
          (ThreeSum.LightReportingSuffixCatalog.stride
            (ThreeSum.BlockIndexedQuery.suffixStage J
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
              k)
            boxCut)))
      dst)
  (hinL : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) inL n) dst)
  (hinR : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) inR n) dst)
  (hdst : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst n) selected)
  (hselected :
    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) selected n) maskBase)
  (hmasks :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maskBase
        (ThreeSum.LightSparseQuery.queryItems (ThreeSum.LightBlockQuery.residualSize h J k) t))
      work)
  (hspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (ThreeSum.LightPascal.tableSize (ThreeSum.LightBlockQuery.width h J)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.LightBlockQuery.width h J)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      lim.space)
  (hpowSpace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (ThreeSum.LightBlockQuery.width h J))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      lim.space)
  (hemodSpace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (Nat.log (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (ThreeSum.LightReportingCatalogLookup.valueBound (ThreeSum.LightBlockQuery.width h J)
                (ThreeSum.LightReportingPrefixCatalog.count h k))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.LightBlockQuery.width h J)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.LightBlockQuery.width h J)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
      lim.word)
  (hlookupWord :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (ThreeSum.LightReportingCatalogLookup.word (ThreeSum.LightBlockQuery.width h J)
          (ThreeSum.LightReportingPrefixCatalog.count h k)))
      lim.word)
  (hvalueWord :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (ThreeSum.LightSparseQuery.magnitudeBound
          (ThreeSum.BlockIndexedQuery.suffixStage J
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
            k)
          (ThreeSum.BlockIndexedQuery.suffixStage J
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
            k)
          (ThreeSum.LightBlockQuery.residualSize h J k) t (@Finset.card.{u_2} β B) (@Finset.card.{u_3} γ C)))
      lim.word)
  (ht :
    @LE.le.{0} Nat instLENat t
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.LightBlockQuery.residualSize h J k)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (hboxCut : @LE.le.{0} Nat instLENat boxCut (ThreeSum.LightBlockQuery.residualSize h J k))
  (hflags :
    @LE.le.{0} Nat instLENat
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (ThreeSum.LightBlockQuery.residualSize h J k) t)
      boxCut)
  (hstoredL :
    @ThreeSum.LightZetaStages.StoredThrough
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
      μ baseL (ThreeSum.LightBlockQuery.sourceCut h J)
      (@ThreeSum.BlockIndexedQuery.leftSource.{u_2} β h J pMod B b
        (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (ThreeSum.GlobalEncoding.GlobalOutput h J)
          (@Prod.snd.{u_1, 0} α
            (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (ThreeSum.GlobalEncoding.GlobalOutput h J))
            w)))
      (ThreeSum.LightBlockQuery.width h J))
  (hstoredR :
    @ThreeSum.LightZetaStages.StoredThrough
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
      μ baseR (ThreeSum.LightBlockQuery.sourceCut h J)
      (@ThreeSum.BlockIndexedQuery.rightSource.{u_3} γ h J pMod shift C c
        (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (ThreeSum.GlobalEncoding.GlobalOutput h J)
          (@Prod.snd.{u_1, 0} α
            (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (ThreeSum.GlobalEncoding.GlobalOutput h J))
            w)))
      (ThreeSum.LightBlockQuery.width h J))
  (hindexData :
    ∃ (S : List.{0} Int),
      And (Light.Seg μ indexBase S)
        (And
          (@List.Perm.{0} Int S
            (ThreeSum.ReportingHostPackedCatalog.codes (ThreeSum.ReportingHostPackedCatalog.prefixKey h J k)
              (ThreeSum.LightReportingPrefixCatalog.count h k)))
          (@List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LE.le.{0} Int Int.instLEInt x1 x2) S)))
  (hptrs :
    Light.SegN μ ptrBase
      (@List.ofFn.{0} Nat (ThreeSum.LightReportingPrefixCatalog.count h k)
        fun (i : Fin (ThreeSum.LightReportingPrefixCatalog.count h k)) =>
        @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) boxBase
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@Fin.val (ThreeSum.LightReportingPrefixCatalog.count h k) i)
            (ThreeSum.LightReportingSuffixCatalog.stride
              (ThreeSum.BlockIndexedQuery.suffixStage J
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                k)
              boxCut))))
  (hboxes :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i (ThreeSum.LightReportingPrefixCatalog.count h k) →
        @ThreeSum.LightBoxStages.StoredThrough
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) J k)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
          μ
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) boxBase
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i
              (ThreeSum.LightReportingSuffixCatalog.stride
                (ThreeSum.BlockIndexedQuery.suffixStage J
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                  k)
                boxCut)))
          boxCut
          (@ThreeSum.ReportingHostSuffix.leafWeight
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) J k)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) k
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
            (@ThreeSum.ReportingHostSuffix.block_fit J
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
              k hk)
            (@ThreeSum.BlockIndexedQuery.leftSource.{u_2} β h J pMod B b
              (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput h J)
                (@Prod.snd.{u_1, 0} α
                  (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (ThreeSum.GlobalEncoding.GlobalOutput h J))
                  w)))
            (@ThreeSum.BlockIndexedQuery.rightSource.{u_3} γ h J pMod shift C c
              (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput h J)
                (@Prod.snd.{u_1, 0} α
                  (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (ThreeSum.GlobalEncoding.GlobalOutput h J))
                  w)))
            (ThreeSum.BlockIndexedQuery.suffixStage J
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
              k)
            (ThreeSum.ReportingHostPrefixOrder.preL h J k i) (ThreeSum.ReportingHostPrefixOrder.preR h J k i))
          (ThreeSum.BlockIndexedQuery.suffixStage J
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
            k))
  (hreadL :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) inL i))
          (@Nat.cast.{0} Int instNatCastInt
            (@ThreeSum.SubsetAddress.subsetMask
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
              (@ThreeSum.BlockIndexedQuery.leftPrefix J
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                k
                (@ThreeSum.StoredReporting.prefixRows J
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                  (pres i))))))
  (hreadR :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) inR i))
          (@Nat.cast.{0} Int instNatCastInt
            (@ThreeSum.SubsetAddress.subsetMask
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
              (@ThreeSum.BlockIndexedQuery.rightPrefix J
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                k
                (@ThreeSum.BlockForced.outputRows h J
                  (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (ThreeSum.GlobalEncoding.GlobalOutput h J)
                    (@Prod.snd.{u_1, 0} α
                      (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (ThreeSum.GlobalEncoding.GlobalOutput h J))
                      w)))
                (@ThreeSum.StoredReporting.prefixRows J
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                  (pres i))))))
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (ThreeSum.LightBlockQuery.width h J)))
        (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
      lim.depth),
  Light.Meets lim ThreeSum.LightReportingCatalogLevel.program
    (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))) depth
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightBlockQuery.width h J))
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightBlockQuery.sourceCut h J))
        (@List.cons.{0} Int
          (@Nat.cast.{0} Int instNatCastInt
            (ThreeSum.BlockIndexedQuery.suffixStage J
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
              k))
          (@List.cons.{0} Int
            (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) (@Nat.cast.{0} Int instNatCastInt k)
              (@Nat.cast.{0} Int instNatCastInt h))
            (@List.cons.{0} Int
              (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) (@Nat.cast.{0} Int instNatCastInt k)
                (@Nat.cast.{0} Int instNatCastInt h))
              (@List.cons.{0} Int
                (@Nat.cast.{0} Int instNatCastInt
                  (ThreeSum.BlockIndexedQuery.suffixStage J
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                    k))
                (@List.cons.{0} Int
                  (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) (@Nat.cast.{0} Int instNatCastInt k)
                    (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                      (@OfNat.ofNat.{0} Int (nat_lit 512) (@instOfNat (nat_lit 512)))
                      (@Nat.cast.{0} Int instNatCastInt h)))
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightBlockQuery.residualSize h J k))
                    (@List.cons.{0} Int
                      (@Nat.cast.{0} Int instNatCastInt
                        (@ThreeSum.SubsetAddress.subsetMask
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                          (@ThreeSum.BlockIndexedQuery.querySet J
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                            k
                            (@ThreeSum.BlockForced.outputRows h J
                              (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                (ThreeSum.GlobalEncoding.GlobalOutput h J)
                                (@Prod.snd.{u_1, 0} α
                                  (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                    (ThreeSum.GlobalEncoding.GlobalOutput h J))
                                  w))))))
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt t)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt baseL)
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt baseR)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt boxCut)
                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt indexBase)
                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt ptrBase)
                                  (@List.cons.{0} Int
                                    (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightReportingPrefixCatalog.count h k))
                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt inL)
                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt inR)
                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt maskBase)
                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt selected)
                                                  (@List.nil.{0} Int))))))))))))))))))))))))
    μ (ThreeSum.LightReportingCatalogLevel.time h J k t n) fun (r : Int) (μ' : Nat → Int) =>
    have counts := fun (i : Nat) =>
      @ThreeSum.RawReporting.prefixQuery.{u_1, u_2, u_3} α β γ inst h J
        (@ThreeSum.RawIncidences.rawOn.{u_1, u_2, u_3} α β γ h J pMod shift
          (@SProd.sprod.{u_1, max u_2 u_3, max (max u_1 u_2) u_3} (Finset.{u_1} α)
            (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ))
            (Finset.{max (max u_2 u_3) u_1} (Prod.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)))
            (@Finset.instSProd.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)) A
            (@SProd.sprod.{u_2, u_3, max u_2 u_3} (Finset.{u_2} β) (Finset.{u_3} γ)
              (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ)) (@Finset.instSProd.{u_2, u_3} β γ) B C))
          a b c)
        w k (pres i);
    And
      (@Eq.{1} Int r
        (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Nat (ThreeSum.LightReportingFilter.selected counts n))))
      (And (Light.SegN μ' selected (ThreeSum.LightReportingFilter.selected counts n))
        (And (Light.SegN μ' dst (@List.ofFn.{0} Nat n fun (i : Fin n) => counts (@Fin.val n i))) (Light.Kept μ μ' dst))) := by
  exact @ThreeSum.LightReportingCatalogLevel.program_meets_sourceProof

#print axioms solution
