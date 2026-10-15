-- Prove2me | solution 1 for ThreeSum.LightBandEnumeration.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:16:34.856758+00:00
-- url     : https://prove2.me/submissions/096cbc00-5f6f-4fce-a8dd-42111ea2c4d5

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_Light_clog2_meets
import Theorems.Thm_Light_powTable_ends
import Theorems.Thm_ThreeSum_KaratsubaInterface_capacity_lt_twice
import Theorems.Thm_ThreeSum_LightBandTable_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace Light.PowTable
end Light.PowTable
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

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

/-- Zeros at the end of the list do not matter. -/
theorem frame_append_zeros (l : List ℤ) (n : ℕ) : frame (l ++ List.replicate n 0) = frame l := by
  funext y
  simp only [frame, List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_replicate]
  split_ifs with h1 h2
  · rfl
  · rw [List.getElem?_eq_none (by omega)]
    rfl
  · rw [List.getElem?_eq_none (by omega)]

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
# Tables of powers

powTable(dst, L, b) writes 1, b, b², …, b^(L-1) into the L cells from dst and changes nothing else,
within `powTableTime L` steps (`powTable_meets`).  The list of these powers is `powList b L`.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}




@[simp] theorem length_powList (b L : ℕ) : (powList b L).length = L := by simp [powList]

@[simp] theorem getElem_powList {b L j : ℕ} (h : j < (powList b L).length) :
    (powList b L)[j] = ((b ^ j : ℕ) : ℤ) := by
  simp [powList]

namespace PowTable









end PowTable

open PowTable


























































/-- **powTable(dst, L, b)** writes the powers 1, b, …, b^(L-1) into the L cells from dst and changes
nothing else. -/
theorem powTable_meets {p : ℕ} (hp : P[p]? = some powTableBody) {μ : ℕ → ℤ} {dst L b : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + L ≤ lim.space)
    (hpow : ∀ j ≤ L, ((b ^ j : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [(dst : ℤ), L, b] μ (powTableTime L) fun _ μ' =>
      Seg μ' dst (powList b L) ∧ SameOutside μ μ' dst L :=
  -- the local variables that are no arguments hold 0
  .of_body hp (frame_append_zeros [(dst : ℤ), L, b] 2 ▸ powTable_ends 0 0 [] hw hdst hpow)

end Light

end
end

section


/-!
# Machine evaluation of compact subset addresses

The current width decreases by one in each recursive call. Its highest
power of two is read from a table, so neither division nor a loop proportional
to the numeric bit-mask value occurs. Pascal coefficients are single reads
from the constructed rectangular table.
-/

namespace ThreeSum.LightSubsetAddress

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal

variable {lim : Limits} {P : Program}




theorem powers_of_segment {μ : ℕ → ℤ} {base W : ℕ}
    (h : Seg μ base (powList 2 (W+1))) : Powers μ base W := by
  intro i hi
  have hs := h i (by simp; omega)
  simpa only [getElem_powList] using hs

























































































































end ThreeSum.LightSubsetAddress

end

section


/-!
# A closed machine program listing all relevant sorted-band candidates

The program computes its own binary width and power table, then executes
exactly the three rectangular owner tables. Every table cell contains an
interval lookup result (index plus one, zero for a miss). The source arrays
remain intact. The coverage theorem below connects these actual memory cells
to every relevant triple, and hence to every exact equation in the bands.
-/

namespace ThreeSum.LightBandEnumeration

set_option maxHeartbeats 1200000
set_option maxRecDepth 4000

open Light ThreeSum.BandEnumeration ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}








theorem At.keep {μ μ' : ℕ → ℤ} {lo hi bound : ℕ} {A : Family}
    (h : At μ lo hi A) (hk : Kept μ μ' bound)
    (hlo : lo+A.size ≤ bound) (hhi : hi+A.size ≤ bound) : At μ' lo hi A := by
  constructor
  · intro i hi
    rw [hk (lo+i) (by omega)]
    exact h.1 i hi
  · intro i hi'
    rw [hk (hi+i) (by omega)]
    exact h.2 i hi'






















































theorem Procs.meets_sourceProof {pMain al ah bl bh cl ch dst U d : ℕ} {μ : ℕ → ℤ}
    (R : Procs P pMain) (A B C : Family)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hal : al+A.size ≤ dst) (hah : ah+A.size ≤ dst)
    (hbl : bl+B.size ≤ dst) (hbh : bh+B.size ≤ dst)
    (hcl : cl+C.size ≤ dst) (hch : ch+C.size ≤ dst)
    (hspace : space dst A.size B.size C.size ≤ lim.space)
    (hword : (word A.size B.size C.size U : ℤ) ≤ lim.word)
    (hd : d+width A.size B.size C.size+4 ≤ lim.depth)
    (hA : At μ al ah A) (hB : At μ bl bh B) (hC : At μ cl ch C)
    (hAU : Bounded A U) (hBU : Bounded B U) (hCU : Bounded C U) :
    Meets lim P pMain d [al,ah,bl,bh,cl,ch,A.size,B.size,C.size,dst] μ
      (time A.size B.size C.size)
      (fun r μ' => r = (count A.size B.size C.size : ℤ) ∧
        Tables μ' dst A B C ∧ Kept μ μ' dst) := by
  let N := A.size+B.size+C.size
  let W := width A.size B.size C.size
  let bc := B.size*C.size
  let ab := A.size*B.size
  let ac := A.size*C.size
  let outAB := dst+bc
  let outAC := outAB+ab
  let powers := outAC+ac
  have hNdef : N = A.size+B.size+C.size := rfl
  have hWdef : W = Nat.clog 2 (N+1) := rfl
  have hspace' : powers+(W+1) ≤ lim.space := by
    simpa [powers,outAC,outAB,bc,ab,ac,W,space,count,Nat.add_assoc] using hspace
  have hWWord : ((width A.size B.size C.size+1 : ℕ) : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (by change W+1 ≤ lim.space; omega)).trans hw
  have hwidthN : Nat.clog 2 (N+1) = width A.size B.size C.size := rfl
  have hcapacity : 2^W < 2*(N+1) := by
    exact KaratsubaInterface.capacity_lt_twice (p := N+1) (by omega)
  have hpow : 2^(W+1) < 4*(N+1) := by rw [pow_succ]; omega
  have hN : N < 2^W := by
    have hp : N+1 ≤ 2^W := Nat.le_pow_clog (by decide) _
    omega
  have hlookupWord : ((N+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word := by
    have hn : N+2^(W+1)+16 ≤ word A.size B.size C.size U := by
      unfold word N at *
      omega
    exact (Int.ofNat_le.mpr hn).trans hword
  have hwordA : ((A.size+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by dsimp [N]; omega)).trans hlookupWord
  have hwordB : ((B.size+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by dsimp [N]; omega)).trans hlookupWord
  have hwordC : ((C.size+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by dsimp [N]; omega)).trans hlookupWord
  have hqueryWord : 2*(U : ℤ) ≤ lim.word := by
    have hh : 2*U ≤ word A.size B.size C.size U := by unfold word; omega
    exact (by exact_mod_cast hh : 2*(U : ℤ) ≤ (word A.size B.size C.size U : ℤ)).trans hword
  have hlogWord : ((2*(N+1)+1 : ℕ) : ℤ) ≤ lim.word := by
    have hh : 2*(N+1)+1 ≤ word A.size B.size C.size U := by unfold word N; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hpowWord (j : ℕ) (hj : j ≤ W+1) : ((2^j : ℕ) : ℤ) ≤ lim.word := by
    have hh : 2^j ≤ 2^(W+1) := Nat.pow_le_pow_right (by decide) hj
    exact (Int.ofNat_le.mpr (by omega : 2^j ≤ N+2^(W+1)+16)).trans hlookupWord
  have hbcNonneg : (0 : ℤ) ≤ (B.size : ℤ)*(C.size : ℤ) := by positivity
  have habNonneg : (0 : ℤ) ≤ (A.size : ℤ)*(B.size : ℤ) := by positivity
  have hacNonneg : (0 : ℤ) ≤ (A.size : ℤ)*(C.size : ℤ) := by positivity
  have hbcWord : (B.size : ℤ)*(C.size : ℤ) ≤ lim.word := by
    exact (by exact_mod_cast (show bc ≤ lim.space by omega) :
      (B.size : ℤ)*(C.size : ℤ) ≤ (lim.space : ℤ)).trans hw
  have habWord : (A.size : ℤ)*(B.size : ℤ) ≤ lim.word := by
    exact (by exact_mod_cast (show ab ≤ lim.space by omega) :
      (A.size : ℤ)*(B.size : ℤ) ≤ (lim.space : ℤ)).trans hw
  have hacWord : (A.size : ℤ)*(C.size : ℤ) ≤ lim.word := by
    exact (by exact_mod_cast (show ac ≤ lim.space by omega) :
      (A.size : ℤ)*(C.size : ℤ) ≤ (lim.space : ℤ)).trans hw
  apply Meets.of_body R.main
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
    (refine Light.Ends.setToThen (N : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, width,
                ← hNdef, ← hWdef, LightBandTable.time, LightBandTable.rowTime,
                LightBandLookup.time, LightBandLookup.searchTime, powTableTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [width, ← hNdef, ← hWdef, LightBandTable.time,
                LightBandTable.rowTime, LightBandLookup.time,
                LightBandLookup.searchTime, powTableTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, width, ← hNdef, ← hWdef,
                LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time,
                LightBandLookup.searchTime, powTableTime] <;>
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
    (refine Light.Ends.setToThen (bc : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, bc,
                width, ← hNdef, ← hWdef, LightBandTable.time,
                LightBandTable.rowTime, LightBandLookup.time,
                LightBandLookup.searchTime, powTableTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [bc, width, ← hNdef, ← hWdef, LightBandTable.time,
                LightBandTable.rowTime, LightBandLookup.time,
                LightBandLookup.searchTime, powTableTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, bc, width, ← hNdef, ← hWdef,
                LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time,
                LightBandLookup.searchTime, powTableTime] <;>
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
    (refine Light.Ends.setToThen (ab : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ab,
                width, ← hNdef, ← hWdef, LightBandTable.time,
                LightBandTable.rowTime, LightBandLookup.time,
                LightBandLookup.searchTime, powTableTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [ab, width, ← hNdef, ← hWdef, LightBandTable.time,
                LightBandTable.rowTime, LightBandLookup.time,
                LightBandLookup.searchTime, powTableTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ab, width, ← hNdef, ← hWdef,
                LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time,
                LightBandLookup.searchTime, powTableTime] <;>
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
    (refine Light.Ends.setToThen (ac : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ac,
                width, ← hNdef, ← hWdef, LightBandTable.time,
                LightBandTable.rowTime, LightBandLookup.time,
                LightBandLookup.searchTime, powTableTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [ac, width, ← hNdef, ← hWdef, LightBandTable.time,
                LightBandTable.rowTime, LightBandLookup.time,
                LightBandLookup.searchTime, powTableTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ac, width, ← hNdef, ← hWdef,
                LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time,
                LightBandLookup.searchTime, powTableTime] <;>
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
    (refine Light.Ends.setToThen (outAB : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, outAB,
                width, ← hNdef, ← hWdef, LightBandTable.time,
                LightBandTable.rowTime, LightBandLookup.time,
                LightBandLookup.searchTime, powTableTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [outAB, width, ← hNdef, ← hWdef, LightBandTable.time,
                LightBandTable.rowTime, LightBandLookup.time,
                LightBandLookup.searchTime, powTableTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, outAB, width, ← hNdef,
                ← hWdef, LightBandTable.time, LightBandTable.rowTime,
                LightBandLookup.time, LightBandLookup.searchTime,
                powTableTime] <;>
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
    (refine Light.Ends.setToThen (outAC : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, outAC,
                width, ← hNdef, ← hWdef, LightBandTable.time,
                LightBandTable.rowTime, LightBandLookup.time,
                LightBandLookup.searchTime, powTableTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [outAC, width, ← hNdef, ← hWdef, LightBandTable.time,
                LightBandTable.rowTime, LightBandLookup.time,
                LightBandLookup.searchTime, powTableTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, outAC, width, ← hNdef,
                ← hWdef, LightBandTable.time, LightBandTable.rowTime,
                LightBandLookup.time, LightBandLookup.searchTime,
                powTableTime] <;>
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
    (refine Light.Ends.setToThen (powers : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, powers,
                width, ← hNdef, ← hWdef, LightBandTable.time,
                LightBandTable.rowTime, LightBandLookup.time,
                LightBandLookup.searchTime, powTableTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [powers, width, ← hNdef, ← hWdef, LightBandTable.time,
                LightBandTable.rowTime, LightBandLookup.time,
                LightBandLookup.searchTime, powTableTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, powers, width, ← hNdef,
                ← hWdef, LightBandTable.time, LightBandTable.rowTime,
                LightBandLookup.time, LightBandLookup.searchTime,
                powTableTime] <;>
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
    (first
      |
        refine
          Light.Ends.callToThen
            ((clog2_meets (d := d + 1) (x := N + 1) R.clog μ hlogWord) _
              (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (clog2_meets (d := d + 1) (x := N + 1) R.clog μ hlogWord) ?_ ?_ ?_
            ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, width,
                ← hNdef, ← hWdef, LightBandTable.time, LightBandTable.rowTime,
                LightBandLookup.time, LightBandLookup.searchTime, powTableTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [width, ← hNdef, ← hWdef, LightBandTable.time,
                LightBandTable.rowTime, LightBandLookup.time,
                LightBandLookup.searchTime, powTableTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, width, ← hNdef, ← hWdef,
                LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time,
                LightBandLookup.searchTime, powTableTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro wid μ₀ ⟨hwid, hmem₀⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  subst μ₀
  rw [← hWdef] at hwid
  subst wid
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
            ((powTable_meets (d := d + 1) (dst := powers) (L := W + 1) (b := 2)
                R.powers hw hspace' hpowWord)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (powTable_meets (d := d + 1) (dst := powers) (L := W + 1) (b := 2)
              R.powers hw hspace' hpowWord)
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, width,
                ← hNdef, ← hWdef, LightBandTable.time, LightBandTable.rowTime,
                LightBandLookup.time, LightBandLookup.searchTime, powTableTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [width, ← hNdef, ← hWdef, LightBandTable.time,
                LightBandTable.rowTime, LightBandLookup.time,
                LightBandLookup.searchTime, powTableTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, width, ← hNdef, ← hWdef,
                LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time,
                LightBandLookup.searchTime, powTableTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro unused μ₁ ⟨hpowersSeg, hkeep₁⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hkept₁ : Kept μ μ₁ dst := fun a ha => hkeep₁ a (Or.inl (by omega))
  have hA₁ := hA.keep hkept₁ hal hah
  have hB₁ := hB.keep hkept₁ hbl hbh
  have hC₁ := hC.keep hkept₁ hcl hch
  have hpowers₁ := powers_of_segment hpowersSeg
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
            ((LightBandTable.meets (d := d + 1) (dst := dst) (s := -1) R.table
                R.row R.lookup R.search μ₁ B.upper C.lower A.lower A.upper hw hbh
                hcl hal hah (by omega) hspace' hwordA hqueryWord hB₁.2 hC₁.1 hA₁.1
                hA₁.2 hpowers₁ A.sorted (by (dsimp [N] at hN); (omega))
                (by norm_num) (fun i hi => (hBU i hi).2)
                (fun i hi => (hCU i hi).1) (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (LightBandTable.meets (d := d + 1) (dst := dst) (s := -1) R.table
              R.row R.lookup R.search μ₁ B.upper C.lower A.lower A.upper hw hbh
              hcl hal hah (by omega) hspace' hwordA hqueryWord hB₁.2 hC₁.1 hA₁.1
              hA₁.2 hpowers₁ A.sorted (by (dsimp [N] at hN); (omega))
              (by norm_num) (fun i hi => (hBU i hi).2) (fun i hi => (hCU i hi).1)
              (by omega))
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, width,
                ← hNdef, ← hWdef, bc, LightBandTable.time, LightBandTable.rowTime,
                LightBandLookup.time, LightBandLookup.searchTime, powTableTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [width, ← hNdef, ← hWdef, bc, LightBandTable.time,
                LightBandTable.rowTime, LightBandLookup.time,
                LightBandLookup.searchTime, powTableTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, width, ← hNdef, ← hWdef, bc,
                LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time,
                LightBandLookup.searchTime, powTableTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro unused μ₂ ⟨hBC, hkeep₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hkept₂ : Kept μ μ₂ dst := fun a ha =>
    (hkeep₂ a (Or.inl ha)).trans (hkept₁ a ha)
  have hA₂ := hA.keep hkept₂ hal hah
  have hB₂ := hB.keep hkept₂ hbl hbh
  have hC₂ := hC.keep hkept₂ hcl hch
  have hpowers₂ : Powers μ₂ powers W := by
    intro i hi
    rw [hkeep₂ (powers+i) (Or.inr (by omega))]
    exact hpowers₁ i hi
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
            ((LightBandTable.meets (d := d + 1) (dst := outAB) (s := 1) R.table
                R.row R.lookup R.search μ₂ A.lower B.lower C.lower C.upper hw
                (by omega) (by omega) (by omega) (by omega) (by omega) hspace'
                hwordC hqueryWord hA₂.1 hB₂.1 hC₂.1 hC₂.2 hpowers₂ C.sorted
                (by (dsimp [N] at hN); (omega)) (by norm_num)
                (fun i hi => (hAU i hi).1) (fun i hi => (hBU i hi).1) (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (LightBandTable.meets (d := d + 1) (dst := outAB) (s := 1) R.table
              R.row R.lookup R.search μ₂ A.lower B.lower C.lower C.upper hw
              (by omega) (by omega) (by omega) (by omega) (by omega) hspace'
              hwordC hqueryWord hA₂.1 hB₂.1 hC₂.1 hC₂.2 hpowers₂ C.sorted
              (by (dsimp [N] at hN); (omega)) (by norm_num)
              (fun i hi => (hAU i hi).1) (fun i hi => (hBU i hi).1) (by omega))
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, width,
                ← hNdef, ← hWdef, bc, ab, outAB, LightBandTable.time,
                LightBandTable.rowTime, LightBandLookup.time,
                LightBandLookup.searchTime, powTableTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [width, ← hNdef, ← hWdef, bc, ab, outAB, LightBandTable.time,
                LightBandTable.rowTime, LightBandLookup.time,
                LightBandLookup.searchTime, powTableTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, width, ← hNdef, ← hWdef, bc,
                ab, outAB, LightBandTable.time, LightBandTable.rowTime,
                LightBandLookup.time, LightBandLookup.searchTime,
                powTableTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro unused μ₃ ⟨hAB, hkeep₃⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hkept₃ : Kept μ μ₃ dst := fun a ha =>
    (hkeep₃ a (Or.inl (by omega))).trans (hkept₂ a ha)
  have hA₃ := hA.keep hkept₃ hal hah
  have hB₃ := hB.keep hkept₃ hbl hbh
  have hC₃ := hC.keep hkept₃ hcl hch
  have hpowers₃ : Powers μ₃ powers W := by
    intro i hi
    rw [hkeep₃ (powers+i) (Or.inr (by omega))]
    exact hpowers₂ i hi
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
            ((LightBandTable.meets (d := d + 1) (dst := outAC) (s := -1) R.table
                R.row R.lookup R.search μ₃ A.lower C.lower B.lower B.upper hw
                (by omega) (by omega) (by omega) (by omega) (by omega) hspace'
                hwordB hqueryWord hA₃.1 hC₃.1 hB₃.1 hB₃.2 hpowers₃ B.sorted
                (by (dsimp [N] at hN); (omega)) (by norm_num)
                (fun i hi => (hAU i hi).1) (fun i hi => (hCU i hi).1) (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (LightBandTable.meets (d := d + 1) (dst := outAC) (s := -1) R.table
              R.row R.lookup R.search μ₃ A.lower C.lower B.lower B.upper hw
              (by omega) (by omega) (by omega) (by omega) (by omega) hspace'
              hwordB hqueryWord hA₃.1 hC₃.1 hB₃.1 hB₃.2 hpowers₃ B.sorted
              (by (dsimp [N] at hN); (omega)) (by norm_num)
              (fun i hi => (hAU i hi).1) (fun i hi => (hCU i hi).1) (by omega))
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, width,
                ← hNdef, ← hWdef, bc, ab, ac, outAB, outAC, LightBandTable.time,
                LightBandTable.rowTime, LightBandLookup.time,
                LightBandLookup.searchTime, powTableTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [width, ← hNdef, ← hWdef, bc, ab, ac, outAB, outAC,
                LightBandTable.time, LightBandTable.rowTime, LightBandLookup.time,
                LightBandLookup.searchTime, powTableTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, width, ← hNdef, ← hWdef, bc,
                ab, ac, outAB, outAC, LightBandTable.time, LightBandTable.rowTime,
                LightBandLookup.time, LightBandLookup.searchTime,
                powTableTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro unused μ₄ ⟨hAC, hkeep₄⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (count A.size B.size C.size : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, count,
                bc, ab, ac, width, ← hNdef, ← hWdef, LightBandTable.time,
                LightBandTable.rowTime, LightBandLookup.time,
                LightBandLookup.searchTime, powTableTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [count, bc, ab, ac, width, ← hNdef, ← hWdef, LightBandTable.time,
                LightBandTable.rowTime, LightBandLookup.time,
                LightBandLookup.searchTime, powTableTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, count, bc, ab, ac, width,
                ← hNdef, ← hWdef, LightBandTable.time, LightBandTable.rowTime,
                LightBandLookup.time, LightBandLookup.searchTime,
                powTableTime] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  refine ⟨rfl,⟨?_,?_,?_⟩,?_⟩
  · intro j hj k hk
    have hoff : j*C.size+k < bc := by
      have hh := Nat.mul_le_mul_right C.size (show j+1 ≤ B.size by omega)
      dsimp [bc]
      nlinarith
    change μ₄ (dst+j*C.size+k) = _
    rw [hkeep₄ _ (Or.inl (by omega)),hkeep₃ _ (Or.inl (by omega))]
    simpa [LightBandTable.rowValue,sub_eq_add_neg,add_comm] using hBC j hj k hk
  · intro i hi j hj
    have hoff : i*B.size+j < ab := by
      have hh := Nat.mul_le_mul_right B.size (show i+1 ≤ A.size by omega)
      dsimp [ab]
      nlinarith
    change μ₄ (dst+bc+i*B.size+j) = _
    rw [hkeep₄ _ (Or.inl (by omega))]
    simpa [LightBandTable.rowValue,outAB] using hAB i hi j hj
  · intro i hi k hk
    simpa [LightBandTable.rowValue,outAC,outAB,bc,ab,sub_eq_add_neg,add_comm] using hAC i hi k hk
  · intro a ha
    change μ₄ a = μ a
    exact (hkeep₄ a (Or.inl (by omega))).trans (hkept₃ a ha)































































































































end ThreeSum.LightBandEnumeration

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {pMain al ah bl bh cl ch dst U d : Nat} {μ : Nat → Int}
  (R : ThreeSum.LightBandEnumeration.Procs P pMain) (A B C : ThreeSum.BandEnumeration.Family),
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) al A.size) dst →
      @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ah A.size) dst →
        @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bl B.size) dst →
          @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bh B.size) dst →
            @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cl C.size) dst →
              @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ch C.size) dst →
                @LE.le.{0} Nat instLENat (ThreeSum.LightBandEnumeration.space dst A.size B.size C.size) lim.space →
                  @LE.le.{0} Int Int.instLEInt
                      (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightBandEnumeration.word A.size B.size C.size U))
                      lim.word →
                    @LE.le.{0} Nat instLENat
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                            (ThreeSum.LightBandEnumeration.width A.size B.size C.size))
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        lim.depth →
                      ThreeSum.LightBandEnumeration.At μ al ah A →
                        ThreeSum.LightBandEnumeration.At μ bl bh B →
                          ThreeSum.LightBandEnumeration.At μ cl ch C →
                            ThreeSum.LightBandEnumeration.Bounded A U →
                              ThreeSum.LightBandEnumeration.Bounded B U →
                                ThreeSum.LightBandEnumeration.Bounded C U →
                                  Light.Meets lim P pMain d
                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt al)
                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt ah)
                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt bl)
                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt bh)
                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cl)
                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt ch)
                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt A.size)
                                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt B.size)
                                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt C.size)
                                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
                                                        (@List.nil.{0} Int)))))))))))
                                    μ (ThreeSum.LightBandEnumeration.time A.size B.size C.size)
                                    fun (r : Int) (μ' : Nat → Int) =>
                                    And
                                      (@Eq.{1} Int r
                                        (@Nat.cast.{0} Int instNatCastInt
                                          (ThreeSum.LightBandEnumeration.count A.size B.size C.size)))
                                      (And (ThreeSum.LightBandEnumeration.Tables μ' dst A B C) (Light.Kept μ μ' dst)) := by
  exact @ThreeSum.LightBandEnumeration.Procs.meets_sourceProof

#print axioms solution
