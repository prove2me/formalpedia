-- Prove2me | solution 1 for ThreeSum.LightPairFlags.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:49:20.775216+00:00
-- url     : https://prove2.me/submissions/d3b62c40-7a10-4589-9bee-77cadbe852d2

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
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle05
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Cast.Order.Ring
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
import Theorems.Thm_Light_Ends_for
import Theorems.Thm_ThreeSum_LightBooleanDot_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_meets
import Theorems.Thm_ThreeSum_LightTrimTest_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
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

theorem Ends.store {σ T a e} {Q : State → Prop} (ha : a.Safe lim σ) (he : e.Safe lim σ)
    (hA : lim.Addr (a.val σ)) (hT : a.cost + e.cost + 1 ≤ T)
    (h : Q { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) }) :
    Ends lim P d (.store a e) σ T Q :=
  ⟨_, _, .store ha he hA, hT, h⟩

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





/-- The natural number behind an address that is a sum of two natural numbers. -/
@[simp] theorem toNat_natCast_add_natCast (a b : ℕ) : ((a : ℤ) + (b : ℤ)).toNat = a + b := by
  rw [← Nat.cast_add, Int.toNat_natCast]

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
                                 | ((ring_nf); (omega)))) : Ends lim P d (s₁ ;; s₂) σ T Q :=
  Ends.seq T₁ (T - T₁) h (by omega)

/-- Brackets do not matter: a piece of several statements, followed by the rest of the program, is
run statement by statement. -/
theorem Ends.seqAssoc {σ : State} {T : ℕ} {s₁ s₂ s₃ : Stmt} {Q : State → Prop}
    (h : Ends lim P d (s₁ ;; (s₂ ;; s₃)) σ T Q) : Ends lim P d ((s₁ ;; s₂) ;; s₃) σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂₃ =>
    cases he₂₃ with
    | seq he₂ he₃ => exact ⟨σ', _, .seq (.seq he₁ he₂) he₃, by omega, hq⟩

/-- A `skip` before the rest of the program takes no step. -/
theorem Ends.skipThen {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop} (h : Ends lim P d s σ T Q) :
    Ends lim P d (.skip ;; s) σ T Q :=
  Ends.seq 0 T (Ends.skip h) (by omega)

/-- A `skip` may be put behind a statement. -/
theorem Ends.skipLast {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop}
    (h : Ends lim P d (s ;; .skip) σ T Q) : Ends lim P d s σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂ =>
    cases he₂
    exact ⟨σ', _, he₁, by omega, hq⟩

/-- A program that is defined as a sequence may be treated as the sequence. -/
theorem Ends.seqSelf {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h : Ends lim P d (s₁ ;; s₂) σ T Q) : Ends lim P d (s₁ ;; s₂) σ T Q :=
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
    Ends lim P d (.set x e ;; s) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.setTo z h he le_rfl) hT

/-- `mem[a] := e`, where a gives the address b, which lies in the memory, and e gives z. -/
theorem Ends.storeTo {a e : Expr} (b : ℕ) (z : ℤ) (h : Q ⟨frame l, Function.update μ b z⟩)
    (he : a.Gives lim ⟨frame l, μ⟩ b ∧ e.Gives lim ⟨frame l, μ⟩ z ∧ b < lim.space := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : a.cost + e.cost + 1 ≤ T := by first
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
    Ends lim P d (.store a e) ⟨frame l, μ⟩ T Q := by
  obtain ⟨⟨ha, hav⟩, ⟨he, hev⟩, hb⟩ := he
  refine Ends.store ha he ?_ hT ?_
  · rw [hav]
    exact ⟨Int.natCast_nonneg b, by exact_mod_cast hb⟩
  · rw [hav, hev, Int.toNat_natCast]
    exact h

/-- `mem[a] := e ; s`, where a gives the address b, which lies in the memory, and e gives z. -/
theorem Ends.storeToThen {a e : Expr} {s : Stmt} (b : ℕ) (z : ℤ)
    (h : Ends lim P d s ⟨frame l, Function.update μ b z⟩ (T - (a.cost + e.cost + 1)) Q)
    (he : a.Gives lim ⟨frame l, μ⟩ b ∧ e.Gives lim ⟨frame l, μ⟩ z ∧ b < lim.space := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : a.cost + e.cost + 1 ≤ T := by first
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
    Ends lim P d (.store a e ;; s) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.storeTo b z h he le_rfl) hT





























































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
    Ends lim P d (.call p args x ;; s) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.callTo hp h ha hd le_rfl) hT

end

end Light

end
end

section


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

/-! ## Regions -/


















/-! ## Memories that agree on some cells -/























variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}




theorem SameOn.refl : SameOn K μ μ := fun _ _ => rfl


















/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}














































/-! ## The tactics -/











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































































































theorem SameOutside.refl : SameOutside μ μ a n := SameOn.refl






/-- Writing inside the region. -/
theorem SameOutside.update (h : SameOutside μ μ' a n) (hb : a ≤ b ∧ b < a + n) (x : ℤ) :
    SameOutside μ (Function.update μ' b x) a n := fun c hc => by
  rw [Function.update_of_ne (by omega)]; exact h c hc

























































































end Light

end
end

section


/-!
# Tactics for proofs about programs

A proof about a program follows the text of the program from top to bottom.  The goal is always
`Ends lim P d s ⟨frame l, μ⟩ T Q`, and the statement at the head of `s` decides what comes next:

| the head of the program | what to write                  | what it is told                       |
|-------------------------|--------------------------------|---------------------------------------|
| `x := e`                | `light_set z`                  | the value `z` of `e`                  |
| `mem[a] := e`           | `light_store b z`              | the address `b` and the value `z`     |
| `if c then … else …`    | `light_if h₁ h₂ : p`           | what the test says, and two names     |
| `x := p(args)`          | `light_call fact with …`       | what the procedure does (`Meets`)     |
| a piece with a lemma    | `light_piece fact with …`      | what the piece does (`Ends`)          |
| `skip`, nothing else    | `light_skip`                   |                                       |
| a loop, nothing else    | `refine Ends.forFrame …`       | invariant and number of rounds        |
| a loop, then more       | `refine Ends.next _ (…)`       | the loop's rule with `(hT := le_rfl)` |

Each tactic works whether or not more program follows, hands the steps that are left to the rest of
the program, and proves the side conditions (the expressions stay within the limits and have the
values that were given, the time suffices) by `light_side` and `light_time`.  What is left is the
goal about the rest of the program, or `Q` of the last state.  After `light_if` there are two goals,
first the one in which the test holds.  The patterns after `with` take apart, as those of `rintro`
do, what holds after the call or the piece.  Goals for holes `?_` in a `fact` come before the goal
about the rest of the program.

The side conditions are decided by linear arithmetic over the hypotheses in the context.
`light_facts H` puts the fields of a record `H` there.  What a side condition needs beyond that is
named after `using`: the content of a cell that is read, a definition to be unfolded, a running time
to be unfolded: `light_set K[j] using hkey`.

A program that is a definition is replaced by its text when a single statement is treated.  A
definition that stands at the head of a sequence stays closed: it is a piece, for `light_piece`.
-/

@[expose] public section

namespace Light

/-! ## Records -/



/-! ## One statement -/





























end Light

end
end

section


/-! # The exact local retained-edge test -/

namespace ThreeSum.LightTrimTest

open Light




theorem flag_le (overlap leftCount rightCount cap : ℕ) : flag overlap leftCount rightCount cap ≤ 1 := by
  unfold flag
  split <;> omega















variable {lim : Limits} {P : Program} {d : ℕ}



























end ThreeSum.LightTrimTest

end

section


/-!
# Constructing every candidate pair's key and trimming flag

All pairs of enumerated local vertices are visited. A zero coordinate-row
inner product tests disjointness; the two actual bucket counts determine
whether the pair survives. The local exhaustive scan is intentionally
unoptimized and its entire arithmetic and lookup cost is charged.
-/

namespace ThreeSum.LightPairFlags

open Light

set_option maxHeartbeats 1500000
set_option maxRecDepth 5000



































variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets_sourceProof {pMain pDivide pDot pTrim : ℕ}
    (hmain : P[pMain]? = some (body pDivide pDot pTrim))
    (hdivide : P[pDivide]? = some LightSmallDivide.body)
    (hdot : P[pDot]? = some LightBooleanDot.body)
    (htrim : P[pTrim]? = some LightTrimTest.body)
    {μ : ℕ → ℤ} {bitPtr leftPtr rightPtr leftHist rightHist dst n L p cap : ℕ}
    (bits : ℕ → ℕ → ℕ) (left right leftCount rightCount : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth) (hn : 0 < n) (hp : 0 < p)
    (hbits : bitPtr+n*L ≤ dst) (hleft : leftPtr+n ≤ dst) (hright : rightPtr+n ≤ dst)
    (hleftHist : leftHist+p ≤ dst) (hrightHist : rightHist+p ≤ dst)
    (hspace : dst+2*(n*n) ≤ lim.space) (hword : (word L n p cap : ℤ) ≤ lim.word)
    (hbitsRead : ∀ i < n, ∀ j < L, μ (bitPtr+i*L+j) = (bits i j : ℤ))
    (hbitsValue : ∀ i < n, ∀ j < L, bits i j ≤ 1)
    (hleftRead : ∀ i < n, μ (leftPtr+i) = (left i : ℤ))
    (hrightRead : ∀ i < n, μ (rightPtr+i) = (right i : ℤ))
    (hleftLt : ∀ i < n, left i < p) (hrightLt : ∀ i < n, right i < p)
    (hleftCount : ∀ r < p, μ (leftHist+r) = (leftCount r : ℤ))
    (hrightCount : ∀ r < p, μ (rightHist+r) = (rightCount r : ℤ))
    (hleftBound : ∀ r < p, leftCount r ≤ n) (hrightBound : ∀ r < p, rightCount r ≤ n) :
    Meets lim P pMain d [bitPtr,leftPtr,rightPtr,leftHist,rightHist,dst,n,L,p,cap] μ (time L n)
      (fun _ μ' =>
        (∀ i < n*n, μ' (dst+i) = (pairKey n p left right i : ℤ)) ∧
        (∀ i < n*n, μ' (dst+n*n+i) = (pairFlag L n cap bits left right leftCount rightCount i : ℤ)) ∧
        SameOutside μ μ' dst (2*(n*n))) := by
  have hbudget (x : ℕ) (hx : x ≤ word L n p cap) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hnWord := hbudget n (by unfold word; omega)
  have hpWord := hbudget p (by unfold word; omega)
  have hcapWord := hbudget cap (by unfold word; omega)
  have hLWord := hbudget L (by unfold word; omega)
  have heWord := hbudget (n*n) (by unfold word; omega)
  have h1Word := hbudget 1 (by unfold word; omega)
  have heWordZ : (n : ℤ)*(n : ℤ) ≤ lim.word := by exact_mod_cast heWord
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
    (refine Light.Ends.setToThen (dst + n * n : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                roundTime, word]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [roundTime, word] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, roundTime, word] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  refine Ends.for (Inv μ bits left right leftCount rightCount
    bitPtr leftPtr rightPtr leftHist rightHist dst n L p cap) (n*n) (roundTime L n) ?_ ?_ ?_ ?_
    (hT := by first
              |
                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, roundTime,
                      LightBooleanDot.time, LightTrimTest.time]);
                  (first
                    | omega
                    | ((ring_nf); (omega))))
              | omega
              |
                (simp [roundTime, LightBooleanDot.time, LightTrimTest.time] <;>
                    first
                    | omega
                    | ((ring_nf); (omega))))
  · refine ⟨0,0,0,0,0,0,μ,?_,?_,?_,SameOutside.refl⟩
    · exact congrArg (fun loc => (⟨loc,μ⟩ : State))
        ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 6).symm)
    · intro j hj; omega
    · intro j hj; omega
  · rintro i _ hi _ ⟨a,b,c,e,f,g,μ',rfl,writtenKeys,writtenFlags,kept⟩
    have hq : i/n < n := (Nat.div_lt_iff_lt_mul hn).mpr hi
    have hr : i%n < n := Nat.mod_lt i hn
    have hqmul : i/n*n ≤ i := Nat.div_mul_le_self i n
    have hqr : i%n+i/n*n = i := by simpa only [Nat.mul_comm] using Nat.mod_add_div i n
    have hdivWord : ((i+n+2 : ℕ) : ℤ) ≤ lim.word :=
      hbudget _ (by unfold word; omega)
    have hdivTime : LightSmallDivide.time i n ≤ 20*n+40 := by unfold LightSmallDivide.time; omega
    have hqWord := hbudget (i/n) (by unfold word; omega)
    have hrWord := hbudget (i%n) (by unfold word; omega)
    have hqNonneg : (0 : ℤ) ≤ (i : ℤ)/(n : ℤ) := by
      rw [← Int.natCast_ediv]
      exact Int.natCast_nonneg _
    have hrem : (i : ℤ)-((i/n : ℕ) : ℤ)*n = ((i%n : ℕ) : ℤ) := by exact_mod_cast (by omega : i-i/n*n=i%n)
    have hqmulZ : ((i/n : ℕ) : ℤ)*(n : ℤ) ≤ lim.word := by
      have hh : i/n*n ≤ word L n p cap := by unfold word; omega
      exact (by exact_mod_cast hh : ((i/n : ℕ) : ℤ)*(n : ℤ) ≤ (word L n p cap : ℤ)).trans hword
    have hqmulInt : (i : ℤ)/(n : ℤ)*n ≤ lim.word := by
      simpa only [Int.natCast_ediv] using hqmulZ
    have hqmulNonneg : (0 : ℤ) ≤ (i : ℤ)/(n : ℤ)*n := by
      rw [← Int.natCast_ediv,← Nat.cast_mul]
      exact Int.natCast_nonneg _
    have hremInt : (i : ℤ)-(i : ℤ)/(n : ℤ)*n = ((i%n : ℕ) : ℤ) := by
      simpa only [Int.natCast_ediv] using hrem
    unfold roundBody
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
              ((LightSmallDivide.meets (d := d + 1) (a := i) (b := n) hdivide μ'
                  hdivWord)
                _ (by omega))
              ?_ ?_ ?_ ?_
        |
          refine
            Light.Ends.callToThen
              (LightSmallDivide.meets (d := d + 1) (a := i) (b := n) hdivide μ'
                hdivWord)
              ?_ ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  roundTime, LightBooleanDot.time, LightTrimTest.time,
                  LightSmallDivide.time]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [roundTime, LightBooleanDot.time, LightTrimTest.time,
                  LightSmallDivide.time] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 => omega);
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, roundTime,
                  LightBooleanDot.time, LightTrimTest.time,
                  LightSmallDivide.time] <;>
                omega)));
      (on_goal -1 =>
          ((rintro qval μ₁ ⟨hqval, hmem₁⟩);
            (try with_unfolding_none refine Light.Ends.skip ?_)))
    subst μ₁
    subst qval
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (i % n : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hremInt,
                  roundTime, LightBooleanDot.time, LightTrimTest.time,
                  LightSmallDivide.time]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hremInt, roundTime, LightBooleanDot.time, LightTrimTest.time,
                  LightSmallDivide.time] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hremInt, roundTime,
                  LightBooleanDot.time, LightTrimTest.time,
                  LightSmallDivide.time] <;>
                omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    have hqL : (i/n+1)*L ≤ n*L := Nat.mul_le_mul_right L (by omega)
    have hrL : (i%n+1)*L ≤ n*L := Nat.mul_le_mul_right L (by omega)
    have hqRow : bitPtr+i/n*L+L ≤ dst := by nlinarith
    have hrRow : bitPtr+i%n*L+L ≤ dst := by nlinarith
    have hqRead : ∀ j < L, μ' (bitPtr+i/n*L+j) = (bits (i/n) j : ℤ) := by
      intro j hj
      rw [kept _ (Or.inl (by omega))]
      exact hbitsRead _ hq j hj
    have hrRead : ∀ j < L, μ' (bitPtr+i%n*L+j) = (bits (i%n) j : ℤ) := by
      intro j hj
      rw [kept _ (Or.inl (by omega))]
      exact hbitsRead _ hr j hj
    have hqLMulWord : (((i/n)*L : ℕ) : ℤ) ≤ lim.word := by
      have hh : (i/n)*L ≤ lim.space := by omega
      exact (Int.ofNat_le.mpr hh).trans hw
    have hrLMulWord : (((i%n)*L : ℕ) : ℤ) ≤ lim.word := by
      have hh : (i%n)*L ≤ lim.space := by omega
      exact (Int.ofNat_le.mpr hh).trans hw
    have hqLInt : (i : ℤ)/(n : ℤ)*L ≤ lim.word := by
      simpa only [Nat.cast_mul,Int.natCast_ediv] using hqLMulWord
    have hqLNonneg : (0 : ℤ) ≤ (i : ℤ)/(n : ℤ)*L := by
      rw [← Int.natCast_ediv,← Nat.cast_mul]
      exact Int.natCast_nonneg _
    have hrLInt : (i : ℤ)%(n : ℤ)*L ≤ lim.word := by
      simpa only [Nat.cast_mul,Int.natCast_emod] using hrLMulWord
    have hrLNonneg : (0 : ℤ) ≤ (i : ℤ)%(n : ℤ)*L := by
      rw [← Int.natCast_emod,← Nat.cast_mul]
      exact Int.natCast_nonneg _
    have hqa : ((bitPtr : ℤ)+((i/n : ℕ) : ℤ)*L).toNat = bitPtr+i/n*L := by
      rw [← Nat.cast_mul,← Nat.cast_add,Int.toNat_natCast]
    have hra : ((bitPtr : ℤ)+((i%n : ℕ) : ℤ)*L).toNat = bitPtr+i%n*L := by
      rw [← Nat.cast_mul,← Nat.cast_add,Int.toNat_natCast]
    have hqaInt : ((bitPtr : ℤ)+(i : ℤ)/(n : ℤ)*L).toNat = bitPtr+i/n*L := by
      simpa only [Int.natCast_ediv] using hqa
    have hraInt : ((bitPtr : ℤ)+(i : ℤ)%(n : ℤ)*L).toNat = bitPtr+i%n*L := by
      simpa only [Int.natCast_emod] using hra
    have hqaBound : (bitPtr : ℤ)+(i : ℤ)/(n : ℤ)*L ≤ lim.word := by
      have hh : ((bitPtr+i/n*L : ℕ) : ℤ) ≤ lim.word := by
        exact (Int.ofNat_le.mpr (by omega : bitPtr+i/n*L ≤ lim.space)).trans hw
      simpa only [Nat.cast_add,Nat.cast_mul,Int.natCast_ediv] using hh
    have hraBound : (bitPtr : ℤ)+(i : ℤ)%(n : ℤ)*L ≤ lim.word := by
      have hh : ((bitPtr+i%n*L : ℕ) : ℤ) ≤ lim.word := by
        exact (Int.ofNat_le.mpr (by omega : bitPtr+i%n*L ≤ lim.space)).trans hw
      simpa only [Nat.cast_add,Nat.cast_mul,Int.natCast_emod] using hh
    have hdotCall := LightBooleanDot.meets (d := d+1) (μ := μ')
      (srcA := bitPtr+i/n*L) (srcB := bitPtr+i%n*L) (n := L)
      hdot (bits (i/n)) (bits (i%n)) hw (by omega) (by omega) hqRead hrRead
      (hbitsValue _ hq) (hbitsValue _ hr) h1Word
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
        | refine Light.Ends.callToThen (hdotCall _ (by omega)) ?_ ?_ ?_ ?_
        | refine Light.Ends.callToThen hdotCall ?_ ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hqa,
                  hra, hqaInt, hraInt, roundTime, LightBooleanDot.time,
                  LightTrimTest.time, LightSmallDivide.time]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hqa, hra, hqaInt, hraInt, roundTime, LightBooleanDot.time,
                  LightTrimTest.time, LightSmallDivide.time] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 => omega);
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hqa, hra, hqaInt, hraInt,
                  roundTime, LightBooleanDot.time, LightTrimTest.time,
                  LightSmallDivide.time] <;>
                omega)));
      (on_goal -1 =>
          ((rintro overlap μ₂ ⟨hoverlap, hmem₂⟩);
            (try with_unfolding_none refine Light.Ends.skip ?_)))
    subst μ₂
    have hlr : μ' (leftPtr+i/n) = (left (i/n) : ℤ) :=
      (kept _ (Or.inl (by omega))).trans (hleftRead _ hq)
    have hrr : μ' (rightPtr+i%n) = (right (i%n) : ℤ) :=
      (kept _ (Or.inl (by omega))).trans (hrightRead _ hr)
    have hlLt := hleftLt _ hq
    have hrLt := hrightLt _ hr
    have hlAddr : ((leftPtr : ℤ)+(i : ℤ)/(n : ℤ)).toNat = leftPtr+i/n := by
      rw [← Int.natCast_ediv,← Nat.cast_add,Int.toNat_natCast]
    have hrAddr : ((rightPtr : ℤ)+(i : ℤ)%(n : ℤ)).toNat = rightPtr+i%n := by
      rw [← Int.natCast_emod,← Nat.cast_add,Int.toNat_natCast]
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (left (i / n) : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hlAddr,
                  hlr, roundTime, LightBooleanDot.time, LightTrimTest.time,
                  LightSmallDivide.time]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hlAddr, hlr, roundTime, LightBooleanDot.time, LightTrimTest.time,
                  LightSmallDivide.time] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hlAddr, hlr, roundTime,
                  LightBooleanDot.time, LightTrimTest.time,
                  LightSmallDivide.time] <;>
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
      (refine Light.Ends.setToThen (right (i % n) : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hrAddr,
                  hrr, roundTime, LightBooleanDot.time, LightTrimTest.time,
                  LightSmallDivide.time]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hrAddr, hrr, roundTime, LightBooleanDot.time, LightTrimTest.time,
                  LightSmallDivide.time] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hrAddr, hrr, roundTime,
                  LightBooleanDot.time, LightTrimTest.time,
                  LightSmallDivide.time] <;>
                omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    have hlc : μ' (leftHist+left (i/n)) = (leftCount (left (i/n)) : ℤ) :=
      (kept _ (Or.inl (by omega))).trans (hleftCount _ hlLt)
    have hrc : μ' (rightHist+right (i%n)) = (rightCount (right (i%n)) : ℤ) :=
      (kept _ (Or.inl (by omega))).trans (hrightCount _ hrLt)
    have hcL := hleftBound _ hlLt
    have hcR := hrightBound _ hrLt
    have ht := LightTrimTest.meets (d := d+1)
      (x := LightBooleanDot.dot (bits (i/n)) (bits (i%n)) L)
      (l := leftCount (left (i/n))) (r := rightCount (right (i%n))) (b := cap)
      htrim μ' h1Word (hbudget _ (by unfold word; omega))
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
        | refine Light.Ends.callToThen (ht _ (by omega)) ?_ ?_ ?_ ?_
        | refine Light.Ends.callToThen ht ?_ ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  hoverlap, hlc, hrc, roundTime, LightBooleanDot.time,
                  LightTrimTest.time, LightSmallDivide.time]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hoverlap, hlc, hrc, roundTime, LightBooleanDot.time,
                  LightTrimTest.time, LightSmallDivide.time] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 => omega);
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hoverlap, hlc, hrc,
                  roundTime, LightBooleanDot.time, LightTrimTest.time,
                  LightSmallDivide.time] <;>
                omega)));
      (on_goal -1 =>
          ((rintro flag μ₃ ⟨hflag, hmem₃⟩);
            (try with_unfolding_none refine Light.Ends.skip ?_)))
    subst μ₃
    have hk : pairKey n p left right i < p*p := by
      unfold pairKey
      nlinarith
    have hkWord := hbudget (pairKey n p left right i) (by unfold word; omega)
    have hkWordZ : (left (i/n) : ℤ)*p+right (i%n) ≤ lim.word := by
      simpa only [pairKey,Nat.cast_add,Nat.cast_mul] using hkWord
    have hprodWord : ((left (i/n)*p : ℕ) : ℤ) ≤ lim.word := by
      have hh : left (i/n)*p ≤ word L n p cap := by unfold pairKey at hk; unfold word; omega
      exact (Int.ofNat_le.mpr hh).trans hword
    have hflag' : flag = (pairFlag L n cap bits left right leftCount rightCount i : ℤ) := hflag
    have hf : pairFlag L n cap bits left right leftCount rightCount i ≤ 1 := LightTrimTest.flag_le ..
    have hfZ : (pairFlag L n cap bits left right leftCount rightCount i : ℤ) ≤ lim.word := by omega
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine
          Light.Ends.storeToThen (dst + i) (pairKey n p left right i : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pairKey,
                  roundTime, LightBooleanDot.time, LightTrimTest.time,
                  LightSmallDivide.time]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [pairKey, roundTime, LightBooleanDot.time, LightTrimTest.time,
                  LightSmallDivide.time] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, pairKey, roundTime,
                  LightBooleanDot.time, LightTrimTest.time,
                  LightSmallDivide.time] <;>
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
      (refine
          Light.Ends.storeToThen (dst + n * n + i)
            (pairFlag L n cap bits left right leftCount rightCount i : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hflag',
                  roundTime, LightBooleanDot.time, LightTrimTest.time,
                  LightSmallDivide.time]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hflag', roundTime, LightBooleanDot.time, LightTrimTest.time,
                  LightSmallDivide.time] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hflag', roundTime,
                  LightBooleanDot.time, LightTrimTest.time,
                  LightSmallDivide.time] <;>
                omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    refine ⟨by simp,(i/n : ℕ),i%n,overlap,left (i/n),right (i%n),flag,
      Function.update (Function.update μ' (dst+i) (pairKey n p left right i : ℤ))
        (dst+n*n+i) (pairFlag L n cap bits left right leftCount rightCount i : ℤ),
      by simp [update_frame_setLocal],?_,?_,?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
        exact writtenKeys j hj
      · rw [Function.update_of_ne (by omega),Function.update_self]
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
        exact writtenFlags j hj
      · rw [Function.update_self]
    · exact (kept.update ⟨by omega,by omega⟩ _).update ⟨by omega,by omega⟩ _
  · rintro _ _ ⟨a,b,c,e,f,g,μ',rfl,writtenKeys,writtenFlags,kept⟩
    exact ⟨writtenKeys,writtenFlags,kept⟩
  · rintro i _ _ _ ⟨a,b,c,e,f,g,μ',rfl,_,_,_⟩
    (((try have := Light.Std.space_le (by assumption)));
      ((try have := Light.Std.const_le (by assumption)));
      (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))



































end ThreeSum.LightPairFlags

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain pDivide pDot pTrim : Nat}
  (hmain :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMain)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightPairFlags.body pDivide pDot pTrim)))
  (hdivide :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pDivide)
      (@Option.some.{0} Light.Stmt ThreeSum.LightSmallDivide.body))
  (hdot :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pDot)
      (@Option.some.{0} Light.Stmt ThreeSum.LightBooleanDot.body))
  (htrim :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pTrim)
      (@Option.some.{0} Light.Stmt ThreeSum.LightTrimTest.body))
  {μ : Nat → Int} {bitPtr leftPtr rightPtr leftHist rightHist dst n L p cap : Nat} (bits : Nat → Nat → Nat)
  (left right leftCount rightCount : Nat → Nat)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd : @LT.lt.{0} Nat instLTNat d lim.depth)
  (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
  (hp : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p)
  (hbits :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bitPtr
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n L))
      dst)
  (hleft : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) leftPtr n) dst)
  (hright : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rightPtr n) dst)
  (hleftHist :
    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) leftHist p) dst)
  (hrightHist :
    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rightHist p) dst)
  (hspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n n)))
      lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightPairFlags.word L n p cap)) lim.word)
  (hbitsRead :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        ∀ (j : Nat),
          @LT.lt.{0} Nat instLTNat j L →
            @Eq.{1} Int
              (μ
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bitPtr
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i L))
                  j))
              (@Nat.cast.{0} Int instNatCastInt (bits i j)))
  (hbitsValue :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        ∀ (j : Nat),
          @LT.lt.{0} Nat instLTNat j L →
            @LE.le.{0} Nat instLENat (bits i j) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (hleftRead :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) leftPtr i))
          (@Nat.cast.{0} Int instNatCastInt (left i)))
  (hrightRead :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rightPtr i))
          (@Nat.cast.{0} Int instNatCastInt (right i)))
  (hleftLt : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i n → @LT.lt.{0} Nat instLTNat (left i) p)
  (hrightLt : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i n → @LT.lt.{0} Nat instLTNat (right i) p)
  (hleftCount :
    ∀ (r : Nat),
      @LT.lt.{0} Nat instLTNat r p →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) leftHist r))
          (@Nat.cast.{0} Int instNatCastInt (leftCount r)))
  (hrightCount :
    ∀ (r : Nat),
      @LT.lt.{0} Nat instLTNat r p →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rightHist r))
          (@Nat.cast.{0} Int instNatCastInt (rightCount r)))
  (hleftBound : ∀ (r : Nat), @LT.lt.{0} Nat instLTNat r p → @LE.le.{0} Nat instLENat (leftCount r) n)
  (hrightBound : ∀ (r : Nat), @LT.lt.{0} Nat instLTNat r p → @LE.le.{0} Nat instLENat (rightCount r) n),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt bitPtr)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt leftPtr)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rightPtr)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt leftHist)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rightHist)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt p)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cap) (@List.nil.{0} Int)))))))))))
    μ (ThreeSum.LightPairFlags.time L n) fun (x : Int) (μ' : Nat → Int) =>
    And
      (∀ (i : Nat),
        @LT.lt.{0} Nat instLTNat i (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n n) →
          @Eq.{1} Int (μ' (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst i))
            (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightPairFlags.pairKey n p left right i)))
      (And
        (∀ (i : Nat),
          @LT.lt.{0} Nat instLTNat i (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n n) →
            @Eq.{1} Int
              (μ'
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n n))
                  i))
              (@Nat.cast.{0} Int instNatCastInt
                (ThreeSum.LightPairFlags.pairFlag L n cap bits left right leftCount rightCount i)))
        (Light.SameOutside μ μ' dst
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n n)))) := by
  exact @ThreeSum.LightPairFlags.meets_sourceProof

#print axioms solution
