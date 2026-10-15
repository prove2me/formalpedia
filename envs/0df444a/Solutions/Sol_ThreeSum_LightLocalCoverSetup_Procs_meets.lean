-- Prove2me | solution 1 for ThreeSum.LightLocalCoverSetup.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:45:10.818444+00:00
-- url     : https://prove2.me/submissions/6cbfa51d-5835-4d40-8c06-9daeee2c5493

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
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
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
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
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
import Theorems.Thm_Light_log2_meets
import Theorems.Thm_ThreeSum_LightLocalCoverBuild_Procs_meets
import Theorems.Thm_ThreeSum_LightNatPower_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightLocalCoverTables
end ThreeSum.LightLocalCoverTables
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds

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


/-! # A packed layout for the complete local-cover constructor -/

namespace ThreeSum.LightLocalCoverLayout

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables






















theorem work_le_space (base h : ℕ) : work base h ≤ space base h := by
  have hm := Nat.le_max_left
    (LightLocalCoverCandidate.space (work base h) (512*h) (vertices h) (localPrime h))
    (scheduleMaps base h+scheduleSize h*(2*(512*h)))
  change LightLocalCoverCandidate.space (work base h) (512*h) (vertices h) (localPrime h) ≤ space base h at hm
  unfold LightLocalCoverCandidate.space at hm
  omega

theorem schedule_end_le_space (base h : ℕ) :
    scheduleMaps base h+scheduleSize h*(2*(512*h)) ≤ space base h := Nat.le_max_right ..

theorem build_meets {lim : Limits} {P : Program} {d pMain : ℕ}
    (S : LightLocalCoverBuild.Procs P pMain) {μ : ℕ → ℤ} {base h : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+7 ≤ lim.depth)
    (hspace : space base h ≤ lim.space) (hword : (LightLocalCoverBuild.word h : ℤ) ≤ lim.word) :
    Meets lim P pMain d
      [512*h,h,localPrime h,rows h,vertices h,localBucketCap h,base,bitPtr base h,maps base h,
        raw0 base h,raw1 base h,hist0 base h,hist1 base h,matrixPtr base h,work base h,
        scheduleSize h,scheduleMaps base h]
      μ (LightLocalCoverBuild.time h)
      (fun r ν => r = (scheduleMaps base h : ℤ) ∧
        Data ν h (maps base h) (hist0 base h) (hist1 base h) (matrixPtr base h) ∧
        ScheduleRows ν h (scheduleMaps base h) ∧
        (∀ s : Occurrence h, ν (candidates base h+s.val) = (candidateAt h s : ℤ)) ∧
        Kept μ ν base) := by
  exact S.meets hw hd ((Nat.le_max_left ..).trans hspace) le_rfl le_rfl le_rfl
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl ((Nat.le_max_right ..).trans hspace) hword

end ThreeSum.LightLocalCoverLayout

end

section


/-!
# The complete local cover from four scalar graph parameters

Only `h`, the selected prime, the vertex count, the bucket cap, and one
starting address are arguments. The candidate count, original schedule
length, and every table address are computed by this fixed program before
it invokes the fully checked local-cover builder.
-/

namespace ThreeSum.LightLocalCoverSetup

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout

set_option maxHeartbeats 2000000
set_option maxRecDepth 6500

































variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets_sourceProof {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {base h : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+8 ≤ lim.depth)
    (hspace : space base h ≤ lim.space) (hword : (word h : ℤ) ≤ lim.word) :
    Meets lim P pMain d [h,localPrime h,vertices h,localBucketCap h,base] μ (time h)
      (fun r ν => r = (scheduleMaps base h : ℤ) ∧
        Data ν h (maps base h) (hist0 base h) (hist1 base h) (matrixPtr base h) ∧
        ScheduleRows ν h (scheduleMaps base h) ∧
        (∀ s : Occurrence h, ν (candidates base h+s.val) = (candidateAt h s : ℤ)) ∧
        Kept μ ν base) := by
  have hbudget (x : ℕ) (hx : x ≤ word h) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hbuildWord := hbudget (LightLocalCoverBuild.word h) (by unfold word; omega)
  have h1024Word := hbudget 1024 (by unfold word; omega)
  have hLWord := hbudget (512*h) (by unfold word; omega)
  have hNWord := hbudget (rows h) (by unfold word; omega)
  have hTWord := hbudget (scheduleSize h) (by unfold word; omega)
  have hcolsWord := hbudget (cols h) (by unfold word; omega)
  have hlogWord := hbudget (2*cols h+2) (by unfold word; omega)
  have hhostLe : LightLocalCoverHost.word h ≤ word h := by
    have hfirst : LightLocalCoverHost.word h ≤ LightLocalCoverBuild.word h := Nat.le_add_right ..
    have hsecond : LightLocalCoverBuild.word h ≤ word h := by unfold word; omega
    exact hfirst.trans hsecond
  have hcoreBudget (x : ℕ) (hx : x ≤ LightLocalCoverHost.word h) : (x : ℤ) ≤ lim.word :=
    hbudget x (hx.trans hhostLe)
  have hwidthWord := hcoreBudget (2*(512*h)) (by
    unfold LightLocalCoverHost.word LightWeightGather.word
    omega)
  have hnWord := hcoreBudget (vertices h) (by
    unfold LightLocalCoverHost.word LightLocalCoverCandidate.word
      LightPairFlags.word vertices
    omega)
  have hpWord := hcoreBudget (localPrime h) (by
    unfold LightLocalCoverHost.word LightLocalCoverCandidate.word
      LightPairFlags.word
    omega)
  have hcapWord := hcoreBudget (localBucketCap h) (by
    unfold LightLocalCoverHost.word LightLocalCoverCandidate.word
      LightPairFlags.word
    omega)
  have hwidthWordZ : (2 : ℤ)*(512*(h : ℤ)) ≤ lim.word := by exact_mod_cast hwidthWord
  have hLWordZ : (512 : ℤ)*h ≤ lim.word := by exact_mod_cast hLWord
  have hp2WordZ : (localPrime h : ℤ)*localPrime h ≤ lim.word := by
    simpa only [cols,Nat.cast_mul] using hcolsWord
  have hcolsEq : (cols h : ℤ) = (localPrime h : ℤ)*localPrime h := by
    simp only [cols,Nat.cast_mul]
  have hp2Nonneg : (0 : ℤ) ≤ (localPrime h : ℤ)*localPrime h := by positivity
  have hlogBound : Nat.log2 (localPrime h^2) ≤ cols h := by
    rw [Nat.log2_eq_log_two]
    exact (Nat.log_le_self 2 (localPrime h^2)).trans (by simp [cols,pow_two])
  have hlogResultWord : ((Nat.log2 (localPrime h^2)+1 : ℕ) : ℤ) ≤ lim.word := by
    apply hbudget
    unfold word
    omega
  have hscale : 320*(2*h+1) ≤ scheduleSize h := by
    change 320*(2*h+1) ≤ 320*(2*h+1)*(Nat.log2 (localPrime h^2)+1)
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hscaleWord : ((320*(2*h+1) : ℕ) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hscale).trans hTWord
  have hscaleWordZ : (320 : ℤ)*(2*(h : ℤ)+1) ≤ lim.word := by exact_mod_cast hscaleWord
  have hroundWordZ : (320 : ℤ)*(2*(h : ℤ)+1)*(Nat.log2 (localPrime h^2)+1) ≤ lim.word := by
    simpa only [scheduleSize,LocalHashMoments.scheduleLength,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
      Nat.cast_ofNat] using hTWord
  have hroundNonneg : (0 : ℤ) ≤ 320*(2*(h : ℤ)+1)*(Nat.log2 (localPrime h^2)+1) := by positivity
  have hworkSpace : work base h ≤ lim.space := (work_le_space base h).trans hspace
  have hschedSpace : scheduleMaps base h+scheduleSize h*(2*(512*h)) ≤ lim.space :=
    (schedule_end_le_space base h).trans hspace
  have hsmall (x : ℕ) (hx : x ≤ work base h) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (hx.trans hworkSpace)).trans hw
  have hbitPtr := hsmall (bitPtr base h) (by
    unfold work matrixPtr hist1 hist0 raw1 raw0 maps
    omega)
  have hmaps := hsmall (maps base h) (by unfold work matrixPtr hist1 hist0 raw1 raw0; omega)
  have hraw0 := hsmall (raw0 base h) (by unfold work matrixPtr hist1 hist0 raw1; omega)
  have hraw1 := hsmall (raw1 base h) (by unfold work matrixPtr hist1 hist0; omega)
  have hhist0 := hsmall (hist0 base h) (by unfold work matrixPtr hist1; omega)
  have hhist1 := hsmall (hist1 base h) (by unfold work matrixPtr; omega)
  have hmatrix := hsmall (matrixPtr base h) (by unfold work; omega)
  have hwork := hsmall (work base h) le_rfl
  have hbase := hsmall base (by unfold work matrixPtr hist1 hist0 raw1 raw0 maps bitPtr; omega)
  have hprodBits := hsmall (vertices h*(512*h)) (by
    unfold work matrixPtr hist1 hist0 raw1 raw0 maps
    omega)
  have hprodRows := hsmall (rows h*(2*(512*h))) (by
    unfold work matrixPtr hist1 hist0 raw1 raw0
    omega)
  have hprodRaw := hsmall (2*vertices h) (by unfold work matrixPtr hist1 hist0; omega)
  have hprodHist := hsmall (rows h*localPrime h) (by unfold work matrixPtr hist1; omega)
  have hprodMatrix := hsmall (rows h*cols h) (by unfold work; omega)
  have hprodBitsZ : (vertices h : ℤ)*(512*(h : ℤ)) ≤ lim.word := by exact_mod_cast hprodBits
  have hprodRowsZ : (rows h : ℤ)*(2*(512*(h : ℤ))) ≤ lim.word := by exact_mod_cast hprodRows
  have hprodHistZ : (rows h : ℤ)*localPrime h ≤ lim.word := by exact_mod_cast hprodHist
  have hprodMatrixZ : (rows h : ℤ)*((localPrime h : ℤ)*localPrime h) ≤ lim.word := by
    simpa only [cols,Nat.cast_mul] using hprodMatrix
  have hbitPtrZ : (base : ℤ)+vertices h ≤ lim.word := by
    simpa only [bitPtr,Nat.cast_add] using hbitPtr
  have hmapsZ : (bitPtr base h : ℤ)+(vertices h : ℤ)*(512*(h : ℤ)) ≤ lim.word := by
    simpa only [maps,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hmaps
  have hraw0Z : (maps base h : ℤ)+(rows h : ℤ)*(2*(512*(h : ℤ))) ≤ lim.word := by
    simpa only [raw0,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hraw0
  have hraw1Z : (raw0 base h : ℤ)+2*(vertices h : ℤ) ≤ lim.word := by
    simpa only [raw1,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hraw1
  have hhist0Z : (raw1 base h : ℤ)+2*(vertices h : ℤ) ≤ lim.word := by
    simpa only [hist0,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hhist0
  have hhist1Z : (hist0 base h : ℤ)+(rows h : ℤ)*localPrime h ≤ lim.word := by
    simpa only [hist1,Nat.cast_add,Nat.cast_mul] using hhist1
  have hmatrixZ : (hist1 base h : ℤ)+(rows h : ℤ)*localPrime h ≤ lim.word := by
    simpa only [matrixPtr,Nat.cast_add,Nat.cast_mul] using hmatrix
  have hworkZ : (matrixPtr base h : ℤ)+(rows h : ℤ)*((localPrime h : ℤ)*localPrime h) ≤ lim.word := by
    simpa only [work,cols,Nat.cast_add,Nat.cast_mul] using hwork
  have hbitsNonneg : (0 : ℤ) ≤ (vertices h : ℤ)*(512*(h : ℤ)) := by positivity
  have hrowsNonneg : (0 : ℤ) ≤ (rows h : ℤ)*(2*(512*(h : ℤ))) := by positivity
  have hhistNonneg : (0 : ℤ) ≤ (rows h : ℤ)*localPrime h := by positivity
  have hmatrixNonneg : (0 : ℤ) ≤ (rows h : ℤ)*((localPrime h : ℤ)*localPrime h) := by positivity
  have hscheduleWord : (scheduleMaps base h : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by omega : scheduleMaps base h ≤ lim.space)).trans hw
  have hscheduleWordZ : (work base h : ℤ)+(localPrime h : ℤ)*localPrime h+(rows h : ℤ)+
      (scheduleSize h : ℤ) ≤ lim.word := by
    simpa only [scheduleMaps,LightCoverGreedy.total,cols,Nat.cast_add,Nat.cast_mul,
      Int.add_assoc] using hscheduleWord
  have hscheduleWork : work base h+cols h+rows h+scheduleSize h = scheduleMaps base h := by
    unfold scheduleMaps LightCoverGreedy.total
    omega
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
    (refine Light.Ends.setToThen (512 * h : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, time] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (2 * (512 * h) : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, time] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  have hpowers : ∀ e ≤ 2*(512*h), (((localPrime h)^e : ℕ) : ℤ) ≤ lim.word := by
    intro e he
    have hp : (localPrime h)^e ≤ rows h := Nat.pow_le_pow_right (localPrime_pos h) he
    exact (Int.ofNat_le.mpr hp).trans hNWord
  have hpower := LightNatPower.meets (d := d+1) (b := localPrime h) (e := 2*(512*h))
    S.power μ hwidthWord hpowers
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
      | refine Light.Ends.callToThen (hpower _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hpower ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, time] <;> omega)));
    (on_goal -1 =>
        ((rintro vc μ₁ ⟨hvc, hmem₁⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  subst μ₁
  have hvc' : vc = (rows h : ℤ) := hvc
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (cols h : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time,
                cols]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [time, cols] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, time, cols] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  have hl := log2_meets (d := d+1) (x := cols h) S.log μ hlogWord
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
      | refine Light.Ends.callToThen (hl _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hl ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time,
                cols]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [time, cols] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, time, cols] <;> omega)));
    (on_goal -1 =>
        ((rintro vl μ₂ ⟨hvl, hmem₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  subst μ₂
  have hvl' : vl = (Nat.log2 (localPrime h^2) : ℤ) := by
    simpa only [Nat.log2_eq_log_two,pow_two,cols] using hvl
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (scheduleSize h : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time,
                hvl', scheduleSize, LocalHashMoments.scheduleLength]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [time, hvl', scheduleSize, LocalHashMoments.scheduleLength] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, time, hvl', scheduleSize,
                LocalHashMoments.scheduleLength] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (bitPtr base h : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time,
                bitPtr]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [time, bitPtr] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, time, bitPtr] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (maps base h : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time,
                maps]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [time, maps] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, time, maps] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (raw0 base h : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time,
                raw0, hvc']);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [time, raw0, hvc'] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, time, raw0, hvc'] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (raw1 base h : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time,
                raw1]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [time, raw1] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, time, raw1] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (hist0 base h : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time,
                hist0]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [time, hist0] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, time, hist0] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (hist1 base h : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time,
                hist1, hvc']);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [time, hist1, hvc'] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, time, hist1, hvc'] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (matrixPtr base h : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time,
                matrixPtr, hvc']);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [time, matrixPtr, hvc'] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, time, matrixPtr, hvc'] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (work base h : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time,
                work, hvc', cols]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [time, work, hvc', cols] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, time, work, hvc', cols] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (scheduleMaps base h : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time,
                hscheduleWork, hvc', cols]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [time, hscheduleWork, hvc', cols] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, time, hscheduleWork, hvc',
                cols] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  have hb := build_meets (d := d+1) (μ := μ) (base := base) (h := h) S.build
    hw (by omega) hspace hbuildWord
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
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time,
                hvc']);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [time, hvc'] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, time, hvc'] <;> omega)));
    (on_goal -1 =>
        ((rintro vb μ₃ ⟨hvb, hdata, hrows, hcandidates, hkept⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  exact ⟨hvb,hdata,hrows,hcandidates,hkept⟩






















end ThreeSum.LightLocalCoverSetup

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (S : ThreeSum.LightLocalCoverSetup.Procs P pMain)
  {μ : Nat → Int} {base h : Nat},
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
        lim.depth →
      @LE.le.{0} Nat instLENat (ThreeSum.LightLocalCoverLayout.space base h) lim.space →
        @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightLocalCoverSetup.word h))
            lim.word →
          Light.Meets lim P pMain d
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt h)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LocalCoverBounds.localPrime h))
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightLocalCoverLayout.vertices h))
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LocalCoverBounds.localBucketCap h))
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt base) (@List.nil.{0} Int))))))
            μ (ThreeSum.LightLocalCoverSetup.time h) fun (r : Int) (ν : Nat → Int) =>
            And (@Eq.{1} Int r (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightLocalCoverLayout.scheduleMaps base h)))
              (And
                (ThreeSum.LightLocalCoverTables.Data ν h (ThreeSum.LightLocalCoverLayout.maps base h)
                  (ThreeSum.LightLocalCoverLayout.hist0 base h) (ThreeSum.LightLocalCoverLayout.hist1 base h)
                  (ThreeSum.LightLocalCoverLayout.matrixPtr base h))
                (And
                  (ThreeSum.LightLocalCoverTables.ScheduleRows ν h (ThreeSum.LightLocalCoverLayout.scheduleMaps base h))
                  (And
                    (∀ (s : ThreeSum.GlobalEncoding.Occurrence h),
                      @Eq.{1} Int
                        (ν
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (ThreeSum.LightLocalCoverLayout.candidates base h)
                            (@Fin.val (ThreeSum.GlobalEncoding.scheduleSize h) s)))
                        (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightLocalCoverSchedule.candidateAt h s)))
                    (Light.Kept μ ν base)))) := by
  exact @ThreeSum.LightLocalCoverSetup.Procs.meets_sourceProof

#print axioms solution
