-- Prove2me | solution 1 for ThreeSum.LightBandLookup.search_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:46:40.342556+00:00
-- url     : https://prove2.me/submissions/4f65003b-d33d-4102-a8ff-e03f10f58d22

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
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
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


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress

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

theorem Ends.ite {σ T c s₁ s₂} {Q : State → Prop} (T' : ℕ) (hs : c.Safe lim σ)
    (h₁ : c.Holds σ → Ends lim P d s₁ σ T' Q) (h₂ : ¬ c.Holds σ → Ends lim P d s₂ σ T' Q)
    (hT : c.cost + 1 + T' ≤ T) : Ends lim P d (.ite c s₁ s₂) σ T Q := by
  by_cases hv : c.Holds σ
  · obtain ⟨σ', k, he, hk, hq⟩ := h₁ hv
    exact ⟨σ', _, .iteTrue hs hv he, by omega, hq⟩
  · obtain ⟨σ', k, he, hk, hq⟩ := h₂ hv
    exact ⟨σ', _, .iteFalse hs hv he, by omega, hq⟩
















































































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












































/-- A branch at the end of the program: both sides get the steps that the test leaves. -/
theorem Ends.iteLast {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h₁ : c.Holds σ → Ends lim P d s₁ σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → Ends lim P d s₂ σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ := by (((try have := Light.Std.space_le (by assumption)));
                                ((try have := Light.Std.const_le (by assumption)));
                                (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) (hT : c.cost + 1 ≤ T := by first
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
    Ends lim P d (.ite c s₁ s₂) σ T Q :=
  Ends.ite _ hs h₁ h₂ (by omega)

/-- A branch, followed by the rest of the program: each side, with the rest of the program behind
it, gets the steps that the test leaves. -/
theorem Ends.iteThen {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ s : Stmt} {Q : State → Prop}
    (h₁ : c.Holds σ → Ends lim P d ((Light.Stmt.seq s₁ s)) σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → Ends lim P d ((Light.Stmt.seq s₂ s)) σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ := by (((try have := Light.Std.space_le (by assumption)));
                                ((try have := Light.Std.const_le (by assumption)));
                                (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) (hT : c.cost + 1 ≤ T := by first
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
    Ends lim P d ((Light.Stmt.seq (.ite c s₁ s₂) s)) σ T Q := by
  by_cases hc : c.Holds σ
  · obtain ⟨σ'', _, he, hk, hq⟩ := h₁ hc
    cases he with
    | seq he₁ he₂ => exact ⟨σ'', _, .seq (.iteTrue hs hc he₁) he₂, by omega, hq⟩
  · obtain ⟨σ'', _, he, hk, hq⟩ := h₂ hc
    cases he with
    | seq he₁ he₂ => exact ⟨σ'', _, .seq (.iteFalse hs hc he₁) he₂, by omega, hq⟩

/-- A branch, followed by the rest of the program, where the test says `p`: the first side is run
under the hypothesis `p`, the second under `¬ p`. -/
theorem Ends.iteIffThen {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ s : Stmt} {Q : State → Prop}
    (p : Prop) (h₁ : p → Ends lim P d ((Light.Stmt.seq s₁ s)) σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ p → Ends lim P d ((Light.Stmt.seq s₂ s)) σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ ∧ (c.Holds σ ↔ p) := by (((try have := Light.Std.space_le (by assumption)));
                                                       ((try have := Light.Std.const_le (by assumption)));
                                                       (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : c.cost + 1 ≤ T := by first
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
                                       | ((ring_nf); (omega)))) : Ends lim P d ((Light.Stmt.seq (.ite c s₁ s₂) s)) σ T Q :=
  Ends.iteThen (fun hc => h₁ (hs.2.1 hc)) (fun hc => h₂ fun hp => hc (hs.2.2 hp)) hs.1 hT

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
# Division-free binary interval lookup in actual machine syntax

The search descends a constructed powers-of-two table and extends a known
prefix by one power at a time. Every tested endpoint is an explicit bounded
memory load. Neither natural-number division nor a function-valued memory
oracle is a machine operation. `search_meets` identifies its returned prefix
with any valid sorted partition, and hence with `BinarySearch.upperBound`.
-/

namespace ThreeSum.LightBandLookup

open Light ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}
















theorem search_meets_sourceProof {pSearch a n powers W : ℕ} {x : ℤ}
    (hprog : P[pSearch]? = some (searchBody pSearch))
    (μ : ℕ → ℤ) (f : ℕ → ℤ) (K : ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+n ≤ lim.space) (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((n+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (a+i) = f i)
    (hpowers : Powers μ powers W)
    (hpart : BinarySearch.Partition f x n K) :
    ∀ L k : ℕ, L ≤ W → k ≤ K → K < k+2^L →
      ∀ d, d+L ≤ lim.depth →
      Meets lim P pSearch d [a,n,x,powers,L,k] μ (searchTime L)
        (fun r μ' => r = (K : ℤ) ∧ μ' = μ) := by
  obtain ⟨hKn,hpre,hpost⟩ := hpart
  have hnWord : (n : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (by omega : n ≤ lim.space)).trans hw
  intro L
  induction L with
  | zero =>
      intro k hL hk hgap d hd
      have heq : k = K := by simp only [Nat.pow_zero] at hgap; omega
      apply Meets.of_body hprog
      unfold searchBody searchTime
      refine Ends.iteLast (fun h => False.elim (by simp at h)) (fun _ => ?_)
      focus
        ((((first
                | refine Light.Ends.seqSelf ?_
                | refine Light.Ends.skipLast ?_));
            (repeat
                with_unfolding_none
                  first
                  | refine Light.Ends.seqAssoc ?_
                  | refine Light.Ends.skipThen ?_)));
        (refine Light.Ends.setToThen (k : ℕ) ?_ ?_ ?_);
        (on_goal -1 =>
            first
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
                  | ((ring_nf); (omega))));
        (on_goal -1 =>
            (((try have := Light.Std.space_le (by assumption)));
              ((try have := Light.Std.const_le (by assumption)));
              (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
        (try with_unfolding_none refine Light.Ends.skip ?_)
      exact ⟨by simp [heq],rfl⟩
  | succ L ih =>
      intro k hL hk hgap d hd
      have hLW : L ≤ W := by omega
      have hpower := hpowers L hLW
      have hpPos : 0 < (2 : ℕ)^L := Nat.two_pow_pos _
      have hpLe : 2^L ≤ 2^(W+1) := Nat.pow_le_pow_right (by decide) (by omega)
      have hmidWord : ((k+2^L : ℕ) : ℤ) ≤ lim.word := by
        exact (Int.ofNat_le.mpr (by omega : k+2^L ≤ n+2^(W+1)+16)).trans hword
      have hmidCast : (k : ℤ)+μ (powers+L) = ((k+2^L : ℕ) : ℤ) := by
        rw [hpower]
        push_cast
        rfl
      have hpowerNonneg : (0 : ℤ) ≤ μ (powers+L) := by
        rw [hpower]
        exact Int.natCast_nonneg _
      have hpowerWord : μ (powers+L) ≤ lim.word := by
        rw [hpower]
        exact (Int.ofNat_le.mpr (by omega : 2^L ≤ n+2^(W+1)+16)).trans hword
      have hmidNonneg : (0 : ℤ) ≤ (k : ℤ)+μ (powers+L) := by omega
      have hmidBound : (k : ℤ)+μ (powers+L) ≤ lim.word := by
        rw [hmidCast]
        exact hmidWord
      have hpowerIntNonneg : (0 : ℤ) ≤ (2 : ℤ)^L := by positivity
      have hmidIntBound : (k : ℤ)+(2 : ℤ)^L ≤ lim.word := by exact_mod_cast hmidWord
      have hdouble : 2^(L+1) = 2^L+2^L := by ring
      rw [hdouble] at hgap
      apply Meets.of_body hprog
      unfold searchBody searchTime
      refine Ends.iteLast (fun _ => ?_) (fun h => False.elim (by simp at h))
      focus
        ((((first
                | refine Light.Ends.seqSelf ?_
                | refine Light.Ends.skipLast ?_));
            (repeat
                with_unfolding_none
                  first
                  | refine Light.Ends.seqAssoc ?_
                  | refine Light.Ends.skipThen ?_)));
        (refine Light.Ends.setToThen (L : ℕ) ?_ ?_ ?_);
        (on_goal -1 =>
            first
            |
              ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                    searchTime]);
                (first
                  | omega
                  | ((ring_nf); (omega))))
            | omega
            |
              (simp [searchTime] <;>
                  first
                  | omega
                  | ((ring_nf); (omega))));
        (on_goal -1 =>
            (((try have := Light.Std.space_le (by assumption)));
              ((try have := Light.Std.const_le (by assumption)));
              (simp [Light.Limits.Addr, abs_le, -abs_mul, searchTime] <;> omega)));
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
        (refine Light.Ends.setToThen (k + 2 ^ L : ℕ) ?_ ?_ ?_);
        (on_goal -1 =>
            first
            |
              ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                    hmidCast, searchTime]);
                (first
                  | omega
                  | ((ring_nf); (omega))))
            | omega
            |
              (simp [hmidCast, searchTime] <;>
                  first
                  | omega
                  | ((ring_nf); (omega))));
        (on_goal -1 =>
            (((try have := Light.Std.space_le (by assumption)));
              ((try have := Light.Std.const_le (by assumption)));
              (simp [Light.Limits.Addr, abs_le, -abs_mul, hmidCast, searchTime] <;>
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
            Light.Ends.iteIffThen (((k + 2 ^ L : ℕ) : ℤ) ≤ (n : ℤ)) (fun hmnZ => ?_)
              (fun hmnZ => ?_) ?_ ?_);
        (on_goal -1 =>
            first
            |
              ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                    searchTime]);
                (first
                  | omega
                  | ((ring_nf); (omega))))
            | omega
            |
              (simp [searchTime] <;>
                  first
                  | omega
                  | ((ring_nf); (omega))));
        (on_goal -1 =>
            (((try have := Light.Std.space_le (by assumption)));
              ((try have := Light.Std.const_le (by assumption)));
              (simp [Light.Limits.Addr, abs_le, -abs_mul, searchTime] <;> omega)));
        (all_goals
            repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)
      · have hmn : k+2^L ≤ n := by exact_mod_cast hmnZ
        have hmRead := hread (k+2^L-1) (by omega)
        have hmAddr : (a : ℤ)+((k+2^L : ℕ) : ℤ)-1 =
            ((a+(k+2^L-1) : ℕ) : ℤ) := by omega
        have hmNat : ((a : ℤ)+((k+2^L : ℕ) : ℤ)-1).toNat =
            a+(k+2^L-1) := by rw [hmAddr,Int.toNat_natCast]
        have hmNat' : ((a : ℤ)+((k : ℤ)+(2 : ℤ)^L)-1).toNat =
            a+(k+2^L-1) := by simpa only [Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat] using hmNat
        have hmIntBound : (a : ℤ)+((k : ℤ)+(2 : ℤ)^L) ≤ lim.word := by
          have hn : a+(k+2^L) ≤ lim.space := by omega
          exact (by exact_mod_cast hn : (a : ℤ)+((k : ℤ)+(2 : ℤ)^L) ≤ (lim.space : ℤ)).trans hw
        have hmIntLower : 1 ≤ (a : ℤ)+((k : ℤ)+(2 : ℤ)^L) := by
          have hp : 0 < (2 : ℤ)^L := by positivity
          omega
        have hmIntSpace : (a : ℤ)+((k : ℤ)+(2 : ℤ)^L) ≤ (lim.space : ℤ) := by
          exact_mod_cast (show a+(k+2^L) ≤ lim.space by omega)
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
              Light.Ends.iteIffThen (x < f (k + 2 ^ L - 1)) (fun htest => ?_)
                (fun htest => ?_) ?_ ?_);
          (on_goal -1 =>
              first
              |
                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hmNat',
                      hmRead, searchTime]);
                  (first
                    | omega
                    | ((ring_nf); (omega))))
              | omega
              |
                (simp [hmNat', hmRead, searchTime] <;>
                    first
                    | omega
                    | ((ring_nf); (omega))));
          (on_goal -1 =>
              (((try have := Light.Std.space_le (by assumption)));
                ((try have := Light.Std.const_le (by assumption)));
                (simp [Light.Limits.Addr, abs_le, -abs_mul, hmNat', hmRead,
                      searchTime] <;>
                    omega)));
          (all_goals
              repeat
                with_unfolding_none
                  first
                  | refine Light.Ends.seqAssoc ?_
                  | refine Light.Ends.skipThen ?_)
        · have hkm : K < k+2^L := by
            by_contra h
            have hh := hpre (k+2^L-1) (by omega)
            omega
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
                    ((ih k hLW hk hkm (d + 1) (by omega)) _ (by omega)) ?_ ?_ ?_ ?_
              |
                refine
                  Light.Ends.callToThen (ih k hLW hk hkm (d + 1) (by omega)) ?_ ?_ ?_ ?_);
            (on_goal -1 =>
                first
                |
                  ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                        searchTime]);
                    (first
                      | omega
                      | ((ring_nf); (omega))))
                | omega
                |
                  (simp [searchTime] <;>
                      first
                      | omega
                      | ((ring_nf); (omega))));
            (on_goal -1 => omega);
            (on_goal -1 =>
                (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, searchTime] <;> omega)));
            (on_goal -1 =>
                ((rintro r μ' ⟨hr, hmem⟩);
                  (try with_unfolding_none refine Light.Ends.skip ?_)))
          exact ⟨hr,hmem⟩
        · have hmk : k+2^L ≤ K := by
            by_contra h
            exact htest (hpost (k+2^L-1) (by omega) (by omega))
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
                    ((ih (k + 2 ^ L) hLW hmk (by omega) (d + 1) (by omega)) _ (by omega))
                    ?_ ?_ ?_ ?_
              |
                refine
                  Light.Ends.callToThen
                    (ih (k + 2 ^ L) hLW hmk (by omega) (d + 1) (by omega)) ?_ ?_ ?_ ?_);
            (on_goal -1 =>
                first
                |
                  ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                        searchTime]);
                    (first
                      | omega
                      | ((ring_nf); (omega))))
                | omega
                |
                  (simp [searchTime] <;>
                      first
                      | omega
                      | ((ring_nf); (omega))));
            (on_goal -1 => omega);
            (on_goal -1 =>
                (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, searchTime] <;> omega)));
            (on_goal -1 =>
                ((rintro r μ' ⟨hr, hmem⟩);
                  (try with_unfolding_none refine Light.Ends.skip ?_)))
          exact ⟨hr,hmem⟩
      · have hkm : K < k+2^L := by omega
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
                  ((ih k hLW hk hkm (d + 1) (by omega)) _ (by omega)) ?_ ?_ ?_ ?_
            |
              refine
                Light.Ends.callToThen (ih k hLW hk hkm (d + 1) (by omega)) ?_ ?_ ?_ ?_);
          (on_goal -1 =>
              first
              |
                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                      searchTime]);
                  (first
                    | omega
                    | ((ring_nf); (omega))))
              | omega
              |
                (simp [searchTime] <;>
                    first
                    | omega
                    | ((ring_nf); (omega))));
          (on_goal -1 => omega);
          (on_goal -1 =>
              (((try have := Light.Std.space_le (by assumption)));
                ((try have := Light.Std.const_le (by assumption)));
                (simp [Light.Limits.Addr, abs_le, -abs_mul, searchTime] <;> omega)));
          (on_goal -1 =>
              ((rintro r μ' ⟨hr, hmem⟩);
                (try with_unfolding_none refine Light.Ends.skip ?_)))
        exact ⟨hr,hmem⟩




















































































end ThreeSum.LightBandLookup

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {pSearch a n powers W : Nat} {x : Int},
  @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pSearch)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightBandLookup.searchBody pSearch)) →
    ∀ (μ f : Nat → Int) (K : Nat),
      @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
        @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a n) lim.space →
          @LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) powers
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) W
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              lim.space →
            @LE.le.{0} Int Int.instLEInt
                (@Nat.cast.{0} Int instNatCastInt
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) W
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))))
                lim.word →
              (∀ (i : Nat),
                  @LT.lt.{0} Nat instLTNat i n →
                    @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a i)) (f i)) →
                ThreeSum.LightSubsetAddress.Powers μ powers W →
                  ThreeSum.BinarySearch.Partition f x n K →
                    ∀ (L k : Nat),
                      @LE.le.{0} Nat instLENat L W →
                        @LE.le.{0} Nat instLENat k K →
                          @LT.lt.{0} Nat instLTNat K
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)) →
                            ∀ (d : Nat),
                              @LE.le.{0} Nat instLENat
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d L) lim.depth →
                                Light.Meets lim P pSearch d
                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
                                      (@List.cons.{0} Int x
                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt powers)
                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt k)
                                              (@List.nil.{0} Int)))))))
                                  μ (ThreeSum.LightBandLookup.searchTime L) fun (r : Int) (μ' : Nat → Int) =>
                                  And (@Eq.{1} Int r (@Nat.cast.{0} Int instNatCastInt K)) (@Eq.{1} (Nat → Int) μ' μ) := by
  exact @ThreeSum.LightBandLookup.search_meets_sourceProof

#print axioms solution
