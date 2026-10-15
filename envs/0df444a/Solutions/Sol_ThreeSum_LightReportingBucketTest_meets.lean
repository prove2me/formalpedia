-- Prove2me | solution 1 for ThreeSum.LightReportingBucketTest.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:12:56.820523+00:00
-- url     : https://prove2.me/submissions/ead77d16-417f-42ce-932c-2d29837661a3

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
import Definitions.Def_ThreeSum1962Source_Bundle06
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
import Mathlib.Data.Finset.Card
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
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
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
import Theorems.Thm_ThreeSum_LightReportingBucketPairs_meets
import Theorems.Thm_ThreeSum_LightSourceBucketSelect_meets
import Theorems.Thm_ThreeSum_SourceBuckets_position_bucket_iff
import Theorems.Thm_ThreeSum_SourceBuckets_position_injective


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightSourceBucketSelect
end ThreeSum.LightSourceBucketSelect
namespace ThreeSum.ReportingHostBucketTest
end ThreeSum.ReportingHostBucketTest
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets

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


/-!
# A linear-time histogram procedure in the benchmark language

The input is an array of already computed residue indices in `[0,p)`.
The output is cleared and incremented once per input item. Multiplicities
are retained, including repeated equal residues.
-/

namespace ThreeSum.LightHistogram

open Light Finset

variable {lim : Limits} {P : Program} {d : ℕ}










theorem count_succ (key : ℕ → ℕ) (r i : ℕ) :
    count key r (i + 1) = count key r i + if key i = r then 1 else 0 := by
  unfold count
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases heq : key i = r
  · rw [if_pos heq, Finset.card_insert_of_notMem (by simp)]
    simp [heq]
  · simp [heq]





























































































end ThreeSum.LightHistogram

end

section


/-!
# Exact positions of original indices in retained residue buckets

Counting-sort positions preserve every input incidence. The resulting fiber
segments contain no repeated physical indices even when input values agree.
All inverse-enumeration reasoning is semantic; the actual scatter program
writes these positions using a cursor and never searches an input band.
-/

namespace ThreeSum.SourceBuckets

open Finset LightHistogram

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000






theorem offset_succ (key : ℕ → ℕ) (N r : ℕ) :
    offset key N (r+1) = offset key N r+count key r N := by
  exact Finset.sum_range_succ _ _

theorem offset_mono (key : ℕ → ℕ) (N : ℕ) : Monotone (offset key N) := by
  intro r s hrs
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hrs)

theorem count_mono (key : ℕ → ℕ) (r : ℕ) : Monotone (count key r) := by
  intro i j hij
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hij))

theorem count_strict {key : ℕ → ℕ} {r i j : ℕ} (hij : i < j) (hkey : key i = r) :
    count key r i < count key r j := by
  have he := count_succ key r i
  simp only [hkey,ite_true] at he
  have hm := count_mono key r (show i+1 ≤ j by omega)
  omega

theorem offset_total {key : ℕ → ℕ} {N M : ℕ} (hkey : ∀ i < N, key i < M) :
    offset key N M = N := by
  unfold offset count
  have he := Finset.card_eq_sum_card_fiberwise
    (f := key) (s := range N) (t := range M)
    (fun i hi => Finset.mem_range.mpr (hkey i (Finset.mem_range.mp hi)))
  simpa only [Finset.card_range] using he.symm

theorem offset_le {key : ℕ → ℕ} {N M r : ℕ} (hkey : ∀ i < N, key i < M) (hr : r ≤ M) :
    offset key N r ≤ N := by
  exact (offset_mono key N hr).trans_eq (offset_total hkey)






theorem position_end {key : ℕ → ℕ} {N i : ℕ} (hi : i < N) :
    position key N i < offset key N (key i+1) := by
  rw [offset_succ]
  exact Nat.add_lt_add_left (count_strict hi rfl) _

theorem position_lt {key : ℕ → ℕ} {N M i : ℕ} (hkey : ∀ i < N, key i < M) (hi : i < N) :
    position key N i < N :=
  (position_end hi).trans_le (offset_le hkey (by have hk := hkey i hi; omega))







































theorem exists_position {key : ℕ → ℕ} {N M : ℕ} (hkey : ∀ i < N, key i < M)
    {t : ℕ} (ht : t < N) : ∃ i < N, position key N i = t := by
  let f : Fin N → Fin N := fun i => ⟨position key N i.val,position_lt hkey i.isLt⟩
  have hf : Function.Injective f := by
    intro i j he
    exact Fin.ext (position_injective i.isLt j.isLt (congrArg Fin.val he))
  obtain ⟨i,hi⟩ := Finite.surjective_of_injective hf ⟨t,ht⟩
  exact ⟨i.val,i.isLt,congrArg Fin.val hi⟩

theorem exists_bucket_position {key : ℕ → ℕ} {N M r t : ℕ}
    (hkey : ∀ i < N, key i < M) (hr : r < M) (ht : t < count key r N) :
    ∃ i < N, key i = r ∧ position key N i = offset key N r+t := by
  have htN : offset key N r+t < N := by
    have he := offset_le hkey (show r+1 ≤ M by omega)
    rw [offset_succ] at he
    omega
  obtain ⟨i,hi,he⟩ := exists_position hkey htN
  refine ⟨i,hi,?_,he⟩
  apply (position_bucket_iff hi).mp
  rw [he,offset_succ]
  omega












theorem Stored.read_bucket {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r t : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M)
    (hr : r < M) (ht : t < count key r N) :
    ∃ i < N, key i = r ∧ position key N i = offset key N r+t ∧
      μ (flat+offset key N r+t) = (i : ℤ) := by
  obtain ⟨i,hi,hki,hpos⟩ := exists_bucket_position hkey hr ht
  refine ⟨i,hi,hki,hpos,?_⟩
  simpa only [hpos,Nat.add_assoc] using H.indices i hi







































end ThreeSum.SourceBuckets

end

section


/-!
# Physical bucket-test semantics and original-index completeness

The selected offset segment contains exactly the original physical indices
in one residue fiber, with an independent endpoint flag. The literal pair
tester therefore recognizes exactly the compatible original value pairs.
-/

namespace ThreeSum.ReportingHostBucketTest

open Light SourceBuckets LightHistogram LightSourceBucketSelect

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000




theorem selected_le (key : ℕ → ℕ) (N r flag : ℕ) :
    countSelected key N r flag ≤ count key r N := by
  unfold countSelected
  split <;> omega

theorem selected_end {key : ℕ → ℕ} {N M r flag : ℕ}
    (hkey : ∀ i < N, key i<M) (hr : r<M) :
    offset key N r+countSelected key N r flag ≤ N := by
  have hend := offset_le hkey (show r+1 ≤ M by omega)
  rw [offset_succ] at hend
  exact (Nat.add_le_add_left (selected_le key N r flag) _).trans hend

theorem selected_read {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r flag j : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i<M)
    (hr : r<M) (hj : j<countSelected key N r flag) :
    index μ flat key N r j<N ∧
      μ (flat+offset key N r+j)=(index μ flat key N r j : ℤ) := by
  obtain ⟨i,hi,_,_,hread⟩ := H.read_bucket hkey hr (hj.trans_le (selected_le key N r flag))
  simp only [index,hread,Int.toNat_natCast]
  exact ⟨hi,trivial⟩















































end ThreeSum.ReportingHostBucketTest

end

section


/-!
# Actual independent bucket selection followed by original tuple testing

The host reads the two retained offset headers, applies each endpoint's
independent flag, and runs the exact original-value Cartesian scanner. Its
time is linear in the actual selected physical pair mass plus a constant.
-/

namespace ThreeSum.LightReportingBucketTest

open Light SourceBuckets LightHistogram LightSourceBucketSelect ReportingHostBucketTest

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

















variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets_sourceProof {pMain pSelect pPairs pRow srcL srcR offsetsL offsetsR flatL flatR NL NR M rL rR flagL flagR work : ℕ}
    {μ : ℕ → ℤ}
    (hmain : P[pMain]?=some (body pSelect pPairs))
    (hselect : P[pSelect]?=some LightSourceBucketSelect.body)
    (hpairs : P[pPairs]?=some (LightReportingBucketPairs.body pRow))
    (hrow : P[pRow]?=some LightReportingBucketRow.body)
    (a : ℤ) (left right : ℕ → ℤ) (keyL keyR : ℕ → ℕ)
    (HL : Stored μ keyL NL M offsetsL flatL) (HR : Stored μ keyR NR M offsetsR flatR)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 ≤ lim.depth)
    (hsrcL : srcL+NL ≤ work) (hsrcR : srcR+NR ≤ work)
    (hoffsetsL : offsetsL+M+1 ≤ work) (hoffsetsR : offsetsR+M+1 ≤ work)
    (hflatL : flatL+NL ≤ work) (hflatR : flatR+NR ≤ work) (hspace : work+4 ≤ lim.space)
    (hkeyL : ∀ i < NL, keyL i<M) (hkeyR : ∀ j < NR, keyR j<M)
    (hrL : rL<M) (hrR : rR<M) (hflagL : flagL≤1) (hflagR : flagR≤1)
    (hreadL : ∀ i < NL, μ (srcL+i)=left i) (hreadR : ∀ j < NR, μ (srcR+j)=right j)
    (hvaluesL : ∀ i < NL, |left i|≤lim.word) (hvaluesR : ∀ j < NR, |right j|≤lim.word)
    (ha : |a|≤lim.word) (htarget : ∀ i < NL, |a+left i|≤lim.word)
    (hcountWord : ((NL*NR : ℕ) : ℤ)≤lim.word) :
    Meets lim P pMain d [a,srcL,srcR,offsetsL,flatL,rL,flagL,offsetsR,flatR,rR,flagR,NL,NR,M,work]
      μ (time keyL keyR NL NR rL rR flagL flagR)
      (fun r ν => r=(testCount μ a left right keyL keyR NL NR flatL flatR rL rR flagL flagR : ℤ) ∧
        SameOutside μ ν work 4) := by
  let startL := offset keyL NL rL
  let startR := offset keyR NR rR
  let nL := countSelected keyL NL rL flagL
  let nR := countSelected keyR NR rR flagR
  have hendL : startL+nL≤NL := selected_end hkeyL hrL
  have hendR : startR+nR≤NR := selected_end hkeyR hrR
  have haBounds := abs_le.mp ha
  have hselectedWord : ((nL*nR : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.mul_le_mul (by omega) (by omega))).trans hcountWord
  apply Meets.of_body hmain
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
    (first
      |
        refine
          Light.Ends.callToThen
            ((LightSourceBucketSelect.meets (d := d + 1) hselect HL hw hoffsetsL
                hflatL (by omega) hkeyL hrL hflagL)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (LightSourceBucketSelect.meets (d := d + 1) hselect HL hw hoffsetsL
              hflatL (by omega) hkeyL hrL hflagL)
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightReportingBucketPairs.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightReportingBucketPairs.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul,
                LightReportingBucketPairs.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro unused μ₁ ⟨hptrL, hlenL, hkeepL⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have HR₁ : Stored μ₁ keyR NR M offsetsR flatR := by
    constructor
    · intro r hr
      exact (hkeepL _ (Or.inl (by omega))).trans (HR.offsets r hr)
    · intro i hi
      have hpos := position_lt hkeyR hi
      exact (hkeepL _ (Or.inl (by omega))).trans (HR.indices i hi)
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
          Light.Ends.callToThen
            ((LightSourceBucketSelect.meets (d := d + 1) (dst := work + 2) hselect
                HR₁ hw (by omega) (by omega) (by omega) hkeyR hrR hflagR)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (LightSourceBucketSelect.meets (d := d + 1) (dst := work + 2) hselect
              HR₁ hw (by omega) (by omega) (by omega) hkeyR hrR hflagR)
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightReportingBucketPairs.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightReportingBucketPairs.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul,
                LightReportingBucketPairs.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro unused μ₂ ⟨hptrR, hlenR, hkeepR⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hkeepBelow (i : ℕ) (hi : i<work) : μ₂ i=μ i :=
    (hkeepR i (Or.inl (by omega))).trans (hkeepL i (Or.inl hi))
  have hptrL' : μ₂ work=((flatL+startL : ℕ) : ℤ) :=
    (hkeepR work (Or.inl (by omega))).trans hptrL
  have hlenL' : μ₂ (work+1)=(nL : ℤ) :=
    (hkeepR (work+1) (Or.inl (by omega))).trans hlenL
  change μ₂ (work+2)=((flatR+startR : ℕ) : ℤ) at hptrR
  change μ₂ (work+2+1)=(nR : ℤ) at hlenR
  have hlenR' : μ₂ (work+3)=(nR : ℤ) := by simpa only [Nat.add_assoc] using hlenR
  have hptrRZ : μ₂ (((work : ℤ)+2).toNat)=((flatR+startR : ℕ) : ℤ) := by
    rw [show ((work : ℤ)+2).toNat=work+2 by omega]
    exact hptrR
  have hlenRZ : μ₂ (((work : ℤ)+3).toNat)=(nR : ℤ) := by
    rw [show ((work : ℤ)+3).toNat=work+3 by omega]
    exact hlenR'
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (flatL + startL : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hptrL',
                LightReportingBucketPairs.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hptrL', LightReportingBucketPairs.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hptrL',
                LightReportingBucketPairs.time] <;>
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
    (refine Light.Ends.setToThen (nL : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hlenL',
                LightReportingBucketPairs.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hlenL', LightReportingBucketPairs.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hlenL',
                LightReportingBucketPairs.time] <;>
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
    (refine Light.Ends.setToThen (flatR + startR : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hptrRZ,
                LightReportingBucketPairs.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hptrRZ, LightReportingBucketPairs.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hptrRZ,
                LightReportingBucketPairs.time] <;>
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
    (refine Light.Ends.setToThen (nR : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hlenRZ,
                LightReportingBucketPairs.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hlenRZ, LightReportingBucketPairs.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hlenRZ,
                LightReportingBucketPairs.time] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  have hreadIL (i : ℕ) (hi : i<nL) :
      μ₂ (flatL+startL+i)=(index μ flatL keyL NL rL i : ℤ) :=
    (hkeepBelow _ (by omega)).trans (selected_read HL hkeyL hrL hi).2
  have hreadIR (i : ℕ) (hi : i<nR) :
      μ₂ (flatR+startR+i)=(index μ flatR keyR NR rR i : ℤ) :=
    (hkeepBelow _ (by omega)).trans (selected_read HR hkeyR hrR hi).2
  have hrun := LightReportingBucketPairs.meets (d := d+1) (μ := μ₂)
    (indicesL := flatL+startL) (indicesR := flatR+startR) hpairs hrow a left right
    (index μ flatL keyL NL rL) (index μ flatR keyR NR rR) hw (by omega)
    (by omega) (by omega) (by omega) (by omega)
    (fun _ hi => (selected_read HL hkeyL hrL hi).1)
    (fun _ hi => (selected_read HR hkeyR hrR hi).1) hreadIL hreadIR
    (fun i hi => (hkeepBelow _ (by omega)).trans (hreadL i hi))
    (fun i hi => (hkeepBelow _ (by omega)).trans (hreadR i hi))
    hvaluesL hvaluesR ha htarget hselectedWord
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
      | refine Light.Ends.callToThen (hrun _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hrun ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightReportingBucketPairs.time, startL, startR, nL, nR]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightReportingBucketPairs.time, startL, startR, nL, nR] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul,
                LightReportingBucketPairs.time, startL, startR, nL, nR] <;>
              omega)));
    (on_goal -1 =>
        ((rintro found ν ⟨hfound, hmem⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  subst ν
  refine ⟨hfound,?_⟩
  intro i hi
  exact (hkeepR i (by rcases hi with hi | hi <;> omega)).trans
    (hkeepL i (by rcases hi with hi | hi <;> omega))



























end ThreeSum.LightReportingBucketTest

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program}
  {d pMain pSelect pPairs pRow srcL srcR offsetsL offsetsR flatL flatR NL NR M rL rR flagL flagR work : Nat}
  {μ : Nat → Int},
  @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMain)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightReportingBucketTest.body pSelect pPairs)) →
    @Eq.{1} (Option.{0} Light.Stmt)
        (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
          (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
          (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pSelect)
        (@Option.some.{0} Light.Stmt ThreeSum.LightSourceBucketSelect.body) →
      @Eq.{1} (Option.{0} Light.Stmt)
          (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
            (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
            (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pPairs)
          (@Option.some.{0} Light.Stmt (ThreeSum.LightReportingBucketPairs.body pRow)) →
        @Eq.{1} (Option.{0} Light.Stmt)
            (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
              (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
              (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pRow)
            (@Option.some.{0} Light.Stmt ThreeSum.LightReportingBucketRow.body) →
          ∀ (a : Int) (left right : Nat → Int) (keyL keyR : Nat → Nat),
            ThreeSum.SourceBuckets.Stored μ keyL NL M offsetsL flatL →
              ThreeSum.SourceBuckets.Stored μ keyR NR M offsetsR flatR →
                @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
                  @LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      lim.depth →
                    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcL NL)
                        work →
                      @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcR NR)
                          work →
                        @LE.le.{0} Nat instLENat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offsetsL M)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            work →
                          @LE.le.{0} Nat instLENat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offsetsR M)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              work →
                            @LE.le.{0} Nat instLENat
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flatL NL) work →
                              @LE.le.{0} Nat instLENat
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flatR NR) work →
                                @LE.le.{0} Nat instLENat
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                                    lim.space →
                                  (∀ (i : Nat), @LT.lt.{0} Nat instLTNat i NL → @LT.lt.{0} Nat instLTNat (keyL i) M) →
                                    (∀ (j : Nat), @LT.lt.{0} Nat instLTNat j NR → @LT.lt.{0} Nat instLTNat (keyR j) M) →
                                      @LT.lt.{0} Nat instLTNat rL M →
                                        @LT.lt.{0} Nat instLTNat rR M →
                                          @LE.le.{0} Nat instLENat flagL
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                                            @LE.le.{0} Nat instLENat flagR
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                                              (∀ (i : Nat),
                                                  @LT.lt.{0} Nat instLTNat i NL →
                                                    @Eq.{1} Int
                                                      (μ
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          srcL i))
                                                      (left i)) →
                                                (∀ (j : Nat),
                                                    @LT.lt.{0} Nat instLTNat j NR →
                                                      @Eq.{1} Int
                                                        (μ
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) srcR j))
                                                        (right j)) →
                                                  (∀ (i : Nat),
                                                      @LT.lt.{0} Nat instLTNat i NL →
                                                        @LE.le.{0} Int Int.instLEInt
                                                          (@abs.{0} Int instLatticeInt Int.instAddGroup (left i))
                                                          lim.word) →
                                                    (∀ (j : Nat),
                                                        @LT.lt.{0} Nat instLTNat j NR →
                                                          @LE.le.{0} Int Int.instLEInt
                                                            (@abs.{0} Int instLatticeInt Int.instAddGroup (right j))
                                                            lim.word) →
                                                      @LE.le.{0} Int Int.instLEInt
                                                          (@abs.{0} Int instLatticeInt Int.instAddGroup a) lim.word →
                                                        (∀ (i : Nat),
                                                            @LT.lt.{0} Nat instLTNat i NL →
                                                              @LE.le.{0} Int Int.instLEInt
                                                                (@abs.{0} Int instLatticeInt Int.instAddGroup
                                                                  (@HAdd.hAdd.{0, 0, 0} Int Int Int
                                                                    (@instHAdd.{0} Int Int.instAdd) a (left i)))
                                                                lim.word) →
                                                          @LE.le.{0} Int Int.instLEInt
                                                              (@Nat.cast.{0} Int instNatCastInt
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat) NL NR))
                                                              lim.word →
                                                            Light.Meets lim P pMain d
                                                              (@List.cons.{0} Int a
                                                                (@List.cons.{0} Int
                                                                  (@Nat.cast.{0} Int instNatCastInt srcL)
                                                                  (@List.cons.{0} Int
                                                                    (@Nat.cast.{0} Int instNatCastInt srcR)
                                                                    (@List.cons.{0} Int
                                                                      (@Nat.cast.{0} Int instNatCastInt offsetsL)
                                                                      (@List.cons.{0} Int
                                                                        (@Nat.cast.{0} Int instNatCastInt flatL)
                                                                        (@List.cons.{0} Int
                                                                          (@Nat.cast.{0} Int instNatCastInt rL)
                                                                          (@List.cons.{0} Int
                                                                            (@Nat.cast.{0} Int instNatCastInt flagL)
                                                                            (@List.cons.{0} Int
                                                                              (@Nat.cast.{0} Int instNatCastInt
                                                                                offsetsR)
                                                                              (@List.cons.{0} Int
                                                                                (@Nat.cast.{0} Int instNatCastInt flatR)
                                                                                (@List.cons.{0} Int
                                                                                  (@Nat.cast.{0} Int instNatCastInt rR)
                                                                                  (@List.cons.{0} Int
                                                                                    (@Nat.cast.{0} Int instNatCastInt
                                                                                      flagR)
                                                                                    (@List.cons.{0} Int
                                                                                      (@Nat.cast.{0} Int instNatCastInt
                                                                                        NL)
                                                                                      (@List.cons.{0} Int
                                                                                        (@Nat.cast.{0} Int
                                                                                          instNatCastInt NR)
                                                                                        (@List.cons.{0} Int
                                                                                          (@Nat.cast.{0} Int
                                                                                            instNatCastInt M)
                                                                                          (@List.cons.{0} Int
                                                                                            (@Nat.cast.{0} Int
                                                                                              instNatCastInt work)
                                                                                            (@List.nil.{0}
                                                                                              Int))))))))))))))))
                                                              μ
                                                              (ThreeSum.LightReportingBucketTest.time keyL keyR NL NR rL
                                                                rR flagL flagR)
                                                              fun (r : Int) (ν : Nat → Int) =>
                                                              And
                                                                (@Eq.{1} Int r
                                                                  (@Nat.cast.{0} Int instNatCastInt
                                                                    (ThreeSum.ReportingHostBucketTest.testCount μ a left
                                                                      right keyL keyR NL NR flatL flatR rL rR flagL
                                                                      flagR)))
                                                                (Light.SameOutside μ ν work
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                    (instOfNatNat (nat_lit 4)))) := by
  exact @ThreeSum.LightReportingBucketTest.meets_sourceProof

#print axioms solution
