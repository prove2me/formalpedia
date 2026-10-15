-- Prove2me | solution 1 for ThreeSum.LightLocalCoverMatrix.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:33:27.796554+00:00
-- url     : https://prove2.me/submissions/89115572-8cc9-4109-b866-19f732dee57b

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
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
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
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
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
import Mathlib.Data.List.Range
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
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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
import Theorems.Thm_Light_Ends_for
import Theorems.Thm_ThreeSum_LightLocalCoverCandidate_Procs_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light

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



































/-! ## The rules -/






/-- More time and a weaker conclusion. -/
theorem Ends.mono {s σ T T' Q Q'} (h : Ends lim P d s σ T Q) (hT : T ≤ T')
    (hQ : ∀ σ', Q σ' → Q' σ') : Ends lim P d s σ T' Q' := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he, hc.trans hT, hQ _ hq⟩







theorem Ends.skip {σ T} {Q : State → Prop} (h : Q σ) : Ends lim P d .skip σ T Q :=
  ⟨σ, 0, .skip, Nat.zero_le _, h⟩

theorem Ends.set {σ T x e} {Q : State → Prop} (hs : e.Safe lim σ) (hT : e.cost + 1 ≤ T)
    (h : Q { σ with loc := Function.update σ.loc x (e.val σ) }) : Ends lim P d (.set x e) σ T Q :=
  ⟨_, _, .set hs, hT, h⟩







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














/-- `x := e`, where e gives z. -/
theorem Ends.setTo {x : ℕ} {e : Expr} (z : ℤ) (h : Q ⟨frame (setLocal l x z), μ⟩)
    (he : e.Gives lim ⟨frame l, μ⟩ z := by (((try have := Light.Std.space_le (by assumption)));
                                                  ((try have := Light.Std.const_le (by assumption)));
                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : e.cost + 1 ≤ T := by first
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
    Ends lim P d (.set x e) ⟨frame l, μ⟩ T Q := by
  refine Ends.set he.1 hT ?_
  rw [he.2]
  simp only [update_frame_setLocal]
  exact h

/-- `x := e ; s`, where e gives z.  The rest s of the text gets the steps that are left. -/
theorem Ends.setToThen {x : ℕ} {e : Expr} {s : Stmt} (z : ℤ)
    (h : Ends lim P d s ⟨frame (setLocal l x z), μ⟩ (T - (e.cost + 1)) Q)
    (he : e.Gives lim ⟨frame l, μ⟩ z := by (((try have := Light.Std.space_le (by assumption)));
                                                  ((try have := Light.Std.const_le (by assumption)));
                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : e.cost + 1 ≤ T := by first
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
    Ends lim P d ((Light.Stmt.seq (.set x e) s)) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.setTo z h he le_rfl) hT



















































































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

/-- More time and a weaker conclusion. -/
theorem Meets.mono (h : Meets lim P p d vals μ T R) (hT : T ≤ T') (hR : ∀ r μ', R r μ' → R' r μ') :
    Meets lim P p d vals μ T' R' := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, hp, he.mono hT fun _ => hR _ _⟩

/-- A specification holds with every larger bound on the time. -/
theorem Meets.mono_time (h : Meets lim P p d vals μ T R) (hT : T ≤ T' := by omega) :
    Meets lim P p d vals μ T' R :=
  h.mono hT fun _ _ hR => hR












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
# Constructing every candidate coefficient, histogram, and cover-matrix row

One literal loop visits the radix candidates in increasing index order.
Temporary raw/residue buffers are reused. All candidate coefficient rows,
both histogram tables, and all Boolean matrix rows remain in memory.
-/

namespace ThreeSum.LightLocalCoverMatrix

open Light

set_option maxHeartbeats 2000000
set_option maxRecDepth 6000






























variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets_sourceProof {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {L n p cap N masks bitPtr maps raw0 raw1 hist0 hist1 dst work : ℕ}
    (mask : ℕ → ℕ) (bits : ℕ → ℕ → ℕ) (w0 w1 : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+5 ≤ lim.depth) (hp : 0 < p) (hn : 0 < n)
    (hspace : LightLocalCoverCandidate.space work L n p ≤ lim.space)
    (hmasks : masks+n ≤ maps) (hbits : bitPtr+n*L ≤ maps) (hmaps : maps+N*(2*L) ≤ raw0)
    (hraw0 : raw0+2*n ≤ raw1) (hraw1 : raw1+2*n ≤ hist0)
    (hhist0 : hist0+N*p ≤ hist1) (hhist1 : hist1+N*p ≤ dst) (hdst : dst+N*(p*p) ≤ work)
    (hword : (LightLocalCoverCandidate.word L n p cap N : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^L)
    (hbitsRead : ∀ i < n, ∀ j < L, μ (bitPtr+i*L+j) = (bits i j : ℤ))
    (hbitsValue : ∀ i < n, ∀ j < L, bits i j ≤ 1)
    (hw0 : ∀ j < N, ∀ i < L, w0 j i = WeightEnumeration.digit p (2*L) j (2*i))
    (hw1 : ∀ j < N, ∀ i < L, w1 j i = WeightEnumeration.digit p (2*L) j (2*i+1)) :
    Meets lim P pMain d [L,p,N,n,cap,masks,bitPtr,maps,raw0,raw1,hist0,hist1,dst,work] μ (time L n p N)
      (fun _ μ' => Tables μ' L n p cap maps hist0 hist1 dst mask bits w0 w1 N ∧ Kept μ μ' maps) := by
  have hwork : work ≤ lim.space := by unfold LightLocalCoverCandidate.space at hspace; omega
  have hbudget (x : ℕ) (hx : x ≤ LightLocalCoverCandidate.word L n p cap N) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hNWord := hbudget N (by
    unfold LightLocalCoverCandidate.word LightWeightDecode.word LightWeightRow.word
    omega)
  have hnWord := hbudget n (by unfold LightLocalCoverCandidate.word LightPairFlags.word; omega)
  have hpWord := hbudget p (by unfold LightLocalCoverCandidate.word LightPairFlags.word; omega)
  have hLWord := hbudget L (by unfold LightLocalCoverCandidate.word LightPairFlags.word; omega)
  have hcapWord := hbudget cap (by unfold LightLocalCoverCandidate.word LightPairFlags.word; omega)
  have hWWord := hbudget (2*L) (by
    unfold LightLocalCoverCandidate.word LightWeightDecode.word LightWeightRow.word
    omega)
  have h2Word := hbudget 2 (by unfold LightLocalCoverCandidate.word LightPairFlags.word; omega)
  have hWWordZ : (2 : ℤ)*L ≤ lim.word := by exact_mod_cast hWWord
  have hp2Word := hbudget (p*p) (by unfold LightLocalCoverCandidate.word LightPairFlags.word; omega)
  have hp2WordZ : (p : ℤ)*p ≤ lim.word := by exact_mod_cast hp2Word
  apply Meets.of_body S.main
  unfold body time
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (p * p : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightLocalCoverCandidate.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightLocalCoverCandidate.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul,
                LightLocalCoverCandidate.time] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  refine Ends.for (Inv μ L n p cap N masks bitPtr maps raw0 raw1 hist0 hist1 dst work mask bits w0 w1)
    N (LightLocalCoverCandidate.time L n p N+192) ?_ ?_ ?_ ?_
    (hT := by first
              |
                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                      LightLocalCoverCandidate.time]);
                  (first
                    | omega
                    | ((ring_nf); (omega))))
              | omega
              |
                (simp [LightLocalCoverCandidate.time] <;>
                    first
                    | omega
                    | ((ring_nf); (omega))))
  · refine ⟨0,μ,?_,?_,fun _ _ => rfl⟩
    · simp [update_frame_setLocal]
    · intro j hj; omega
  · rintro i _ hi _ ⟨r,μ',rfl,written,kept⟩
    have himaps := Nat.mul_le_mul_right (2*L) (show i+1 ≤ N by omega)
    have hihist := Nat.mul_le_mul_right p (show i+1 ≤ N by omega)
    have himatrix := Nat.mul_le_mul_right (p*p) (show i+1 ≤ N by omega)
    simp only [Nat.add_mul,one_mul] at himaps hihist himatrix
    have hcoef : maps+i*(2*L)+2*L ≤ raw0 := by omega
    have hlhist : hist0+i*p+p ≤ hist1+i*p := by omega
    have hrhist : hist1+i*p+p ≤ dst+i*(p*p) := by omega
    have hrow : dst+i*(p*p)+p*p ≤ work := by omega
    have hmulCoef : ((i*(2*L) : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (by omega : i*(2*L) ≤ lim.space)).trans hw
    have hmulHist : ((i*p : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (by omega : i*p ≤ lim.space)).trans hw
    have hmulMatrix : ((i*(p*p) : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (by omega : i*(p*p) ≤ lim.space)).trans hw
    have hcoefAddr : ((maps : ℤ)+(i : ℤ)*(2*(L : ℤ))).toNat = maps+i*(2*L) := by
      norm_cast
    have hlhistAddr : ((hist0 : ℤ)+(i : ℤ)*p).toNat = hist0+i*p := by norm_cast
    have hrhistAddr : ((hist1 : ℤ)+(i : ℤ)*p).toNat = hist1+i*p := by norm_cast
    have hmatrixAddr : ((dst : ℤ)+(i : ℤ)*((p : ℤ)*p)).toNat = dst+i*(p*p) := by norm_cast
    have hmask' : ∀ j < n, μ' (masks+j) = (mask j : ℤ) := by
      intro j hj
      rw [kept _ (by omega)]
      exact hmaskRead j hj
    have hbits' : ∀ a < n, ∀ j < L, μ' (bitPtr+a*L+j) = (bits a j : ℤ) := by
      intro a ha j hj
      have hm := Nat.mul_le_mul_right L (show a+1 ≤ n by omega)
      simp only [Nat.add_mul,one_mul] at hm
      have hab : bitPtr+a*L+j < maps := by omega
      rw [kept _ hab]
      exact hbitsRead a ha j hj
    have hword' : (LightLocalCoverCandidate.word L n p cap i : ℤ) ≤ lim.word := by
      apply hbudget
      unfold LightLocalCoverCandidate.word LightWeightDecode.word LightWeightRow.word
      omega
    have htime' : LightLocalCoverCandidate.time L n p i ≤ LightLocalCoverCandidate.time L n p N := by
      unfold LightLocalCoverCandidate.time LightWeightDecode.time LightWeightRow.time LightRadixDigit.time
      gcongr
    have hcall := S.candidate.meets (d := d+1) (μ := μ') (L := L) (n := n) (p := p) (cap := cap)
      (index := i) (masks := masks) (bitPtr := bitPtr) (coef := maps+i*(2*L))
      (raw0 := raw0) (raw1 := raw1) (hist0 := hist0+i*p) (hist1 := hist1+i*p)
      (dst := dst+i*(p*p)) (work := work) mask (w0 i) (w1 i) bits
      hw (by omega) hp hn hspace (by omega) (by omega) hcoef hraw0 (by omega) hlhist hrhist hrow
      hword' hmask' hmaskLt hbits' hbitsValue (hw0 i hi) (hw1 i hi)
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
        |
          refine
            Light.Ends.callToThen ((hcall.mono_time htime') _ (by omega)) ?_ ?_ ?_
              ?_
        | refine Light.Ends.callToThen (hcall.mono_time htime') ?_ ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  hcoefAddr, hlhistAddr, hrhistAddr, hmatrixAddr,
                  LightLocalCoverCandidate.time]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hcoefAddr, hlhistAddr, hrhistAddr, hmatrixAddr,
                  LightLocalCoverCandidate.time] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 => omega);
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hcoefAddr, hlhistAddr,
                  hrhistAddr, hmatrixAddr, LightLocalCoverCandidate.time] <;>
                omega)));
      (on_goal -1 =>
          ((rintro value μ₁ ⟨hcoeffs, hcounts, hentry, hpres⟩);
            (try with_unfolding_none refine Light.Ends.skip ?_)))
    have hprevCoef : ∀ j < i, ∀ a < 2*L,
        μ₁ (maps+j*(2*L)+a) = μ' (maps+j*(2*L)+a) := by
      intro j hj a ha
      have hjm := Nat.mul_le_mul_right (2*L) (show j+1 ≤ i by omega)
      simp only [Nat.add_mul,one_mul] at hjm
      have hbefore : maps+j*(2*L)+a < maps+i*(2*L) := by omega
      exact hpres _ (by omega) (Or.inl hbefore) (Or.inl (by omega)) (Or.inl (by omega))
        (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
    have hprevLeft : ∀ j < i, ∀ a < p,
        μ₁ (hist0+j*p+a) = μ' (hist0+j*p+a) := by
      intro j hj a ha
      have hjm := Nat.mul_le_mul_right p (show j+1 ≤ i by omega)
      simp only [Nat.add_mul,one_mul] at hjm
      have hbefore : hist0+j*p+a < hist0+i*p := by omega
      have hbound : hist0+j*p+a < hist1 := by omega
      exact hpres _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
        (Or.inl hbefore) (Or.inl (by omega)) (Or.inl (by omega))
    have hprevRight : ∀ j < i, ∀ a < p,
        μ₁ (hist1+j*p+a) = μ' (hist1+j*p+a) := by
      intro j hj a ha
      have hjm := Nat.mul_le_mul_right p (show j+1 ≤ i by omega)
      simp only [Nat.add_mul,one_mul] at hjm
      have hbefore : hist1+j*p+a < hist1+i*p := by omega
      have hbound : hist1+j*p+a < dst := by omega
      have hleft : hist0+i*p+p ≤ hist1 := by omega
      exact hpres _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
        (Or.inr (by omega)) (Or.inl hbefore) (Or.inl (by omega))
    have hprevMatrix : ∀ j < i, ∀ a < p*p,
        μ₁ (dst+j*(p*p)+a) = μ' (dst+j*(p*p)+a) := by
      intro j hj a ha
      have hjm := Nat.mul_le_mul_right (p*p) (show j+1 ≤ i by omega)
      simp only [Nat.add_mul,one_mul] at hjm
      have hbefore : dst+j*(p*p)+a < dst+i*(p*p) := by omega
      have hleft : hist0+i*p+p ≤ hist1 := by omega
      have hright : hist1+i*p+p ≤ dst := by omega
      exact hpres _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
        (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl hbefore)
    refine ⟨by simp,value,μ₁,by simp [update_frame_setLocal],?_,?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · obtain ⟨hc,hh,he⟩ := written j hj
        refine ⟨?_,?_,?_⟩
        · intro a ha
          constructor
          · rw [hprevCoef j hj a (by omega)]
            exact (hc a ha).1
          · have ha' : L+a < 2*L := by omega
            have hkeep := hprevCoef j hj (L+a) ha'
            rw [← Nat.add_assoc] at hkeep
            rw [hkeep]
            exact (hc a ha).2
        · intro a ha
          rw [hprevLeft j hj a ha,hprevRight j hj a ha]
          exact hh a ha
        · intro a ha
          rw [hprevMatrix j hj a ha]
          exact he a ha
      · exact ⟨hcoeffs,hcounts,hentry⟩
    · intro a ha
      rw [hpres a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
        (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))]
      exact kept a ha
  · rintro _ _ ⟨r,μ',rfl,written,kept⟩
    exact ⟨written,kept⟩
  · rintro i _ _ _ ⟨r,μ',rfl,_,_⟩
    (((try have := Light.Std.space_le (by assumption)));
      ((try have := Light.Std.const_le (by assumption)));
      (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))














end ThreeSum.LightLocalCoverMatrix

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (S : ThreeSum.LightLocalCoverMatrix.Procs P pMain)
  {μ : Nat → Int} {L n p cap N masks bitPtr maps raw0 raw1 hist0 hist1 dst work : Nat} (mask : Nat → Nat)
  (bits w0 w1 : Nat → Nat → Nat),
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d L)
          (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
        lim.depth →
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p →
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
          @LE.le.{0} Nat instLENat (ThreeSum.LightLocalCoverCandidate.space work L n p) lim.space →
            @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) masks n) maps →
              @LE.le.{0} Nat instLENat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bitPtr
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n L))
                  maps →
                @LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) N
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)))
                    raw0 →
                  @LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) raw0
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
                      raw1 →
                    @LE.le.{0} Nat instLENat
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) raw1
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
                        hist0 →
                      @LE.le.{0} Nat instLENat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) hist0
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) N p))
                          hist1 →
                        @LE.le.{0} Nat instLENat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) hist1
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) N p))
                            dst →
                          @LE.le.{0} Nat instLENat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) N
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p p)))
                              work →
                            @LE.le.{0} Int Int.instLEInt
                                (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightLocalCoverCandidate.word L n p cap N))
                                lim.word →
                              (∀ (i : Nat),
                                  @LT.lt.{0} Nat instLTNat i n →
                                    @Eq.{1} Int
                                      (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) masks i))
                                      (@Nat.cast.{0} Int instNatCastInt (mask i))) →
                                (∀ (i : Nat),
                                    @LT.lt.{0} Nat instLTNat i n →
                                      @LT.lt.{0} Nat instLTNat (mask i)
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)) →
                                  (∀ (i : Nat),
                                      @LT.lt.{0} Nat instLTNat i n →
                                        ∀ (j : Nat),
                                          @LT.lt.{0} Nat instLTNat j L →
                                            @Eq.{1} Int
                                              (μ
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    bitPtr
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i
                                                      L))
                                                  j))
                                              (@Nat.cast.{0} Int instNatCastInt (bits i j))) →
                                    (∀ (i : Nat),
                                        @LT.lt.{0} Nat instLTNat i n →
                                          ∀ (j : Nat),
                                            @LT.lt.{0} Nat instLTNat j L →
                                              @LE.le.{0} Nat instLENat (bits i j)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                      (∀ (j : Nat),
                                          @LT.lt.{0} Nat instLTNat j N →
                                            ∀ (i : Nat),
                                              @LT.lt.{0} Nat instLTNat i L →
                                                @Eq.{1} Nat (w0 j i)
                                                  (ThreeSum.WeightEnumeration.digit p
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)
                                                    j
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                      i))) →
                                        (∀ (j : Nat),
                                            @LT.lt.{0} Nat instLTNat j N →
                                              ∀ (i : Nat),
                                                @LT.lt.{0} Nat instLTNat i L →
                                                  @Eq.{1} Nat (w1 j i)
                                                    (ThreeSum.WeightEnumeration.digit p
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)
                                                      j
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          i)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                          (instOfNatNat (nat_lit 1)))))) →
                                          Light.Meets lim P pMain d
                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt p)
                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt N)
                                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
                                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cap)
                                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt masks)
                                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt bitPtr)
                                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt maps)
                                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt raw0)
                                                              (@List.cons.{0} Int
                                                                (@Nat.cast.{0} Int instNatCastInt raw1)
                                                                (@List.cons.{0} Int
                                                                  (@Nat.cast.{0} Int instNatCastInt hist0)
                                                                  (@List.cons.{0} Int
                                                                    (@Nat.cast.{0} Int instNatCastInt hist1)
                                                                    (@List.cons.{0} Int
                                                                      (@Nat.cast.{0} Int instNatCastInt dst)
                                                                      (@List.cons.{0} Int
                                                                        (@Nat.cast.{0} Int instNatCastInt work)
                                                                        (@List.nil.{0} Int)))))))))))))))
                                            μ (ThreeSum.LightLocalCoverMatrix.time L n p N)
                                            fun (x : Int) (μ' : Nat → Int) =>
                                            And
                                              (ThreeSum.LightLocalCoverMatrix.Tables μ' L n p cap maps hist0 hist1 dst
                                                mask bits w0 w1 N)
                                              (Light.Kept μ μ' maps) := by
  exact @ThreeSum.LightLocalCoverMatrix.Procs.meets_sourceProof

#print axioms solution
