-- Prove2me | solution 1 for ThreeSum.LightSourceRowFlag.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:02:19.857981+00:00
-- url     : https://prove2.me/submissions/d87b53f9-e353-48f3-b828-fba7b0b391c5

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
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
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
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_Light_emod_meets
import Theorems.Thm_ThreeSum_LightSourceFlagTest_meets
import Theorems.Thm_ThreeSum_LightSourceRowScan_meets


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
    Ends lim P d ((Light.Stmt.seq (.store a e) s)) ⟨frame l, μ⟩ T Q :=
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
    Ends lim P d ((Light.Stmt.seq (.call p args x) s)) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.callTo hp h ha hd le_rfl) hT

end

end Light

end
end

section


/-!
# The remainder of a division

emod(x, M, fr) returns the remainder of the integer x modulo M ≥ 1, a number in 0, …, M - 1.  The
language has no division: the routine writes M, 2M, 4M, … into a table at the free pointer fr as
long as they are at most |x|, subtracts them from |x| from the largest down where possible, and
corrects the sign (`emod_meets`).  With k = `emodRounds |x| M` doublings it takes `emodTime |x| M`
steps, a constant times k + 1, and k cells.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}
namespace Emod










end Emod

















































/-- There are at most log₂ (V + 1) + 1 doublings for a number up to V. -/
theorem emodRounds_le {a M V : ℕ} (ha : a ≤ V) : emodRounds a M ≤ Nat.log 2 (V + 1) + 1 := by
  rw [emodRounds, Nat.size_le]
  calc a / M ≤ a := Nat.div_le_self _ _
    _ < V + 1 := by omega
    _ < 2 ^ (Nat.log 2 (V + 1) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _

















namespace Emod













variable {μ : ℕ → ℤ} {x : ℤ} {Mo V fr a : ℕ}










































































































































end Emod

end Light

end
end

section


/-!
# Costed signed residue conversion

This loop uses the benchmark's proved division-free remainder procedure.
Its sign argument supports either an ordinary histogram or a histogram of
the negated original integers. All source multiplicities are retained.
The logarithmic scratch region is reused for each input element.
-/

namespace ThreeSum.LightResidues

open Light

variable {lim : Limits} {P : Program} {d : ℕ}



theorem residue_cast {p : ℕ} (hp : 0 < p) (c x : ℤ) :
    (residue p c x : ℤ) = (c * x) % (p : ℤ) := by
  apply Int.toNat_of_nonneg
  exact Int.emod_nonneg _ (by exact_mod_cast hp.ne')

theorem residue_lt {p : ℕ} (hp : 0 < p) (c x : ℤ) : residue p c x < p := by
  have h := Int.emod_lt_of_pos (c * x) (by exact_mod_cast hp : (0 : ℤ) < p)
  rw [← residue_cast hp] at h
  exact_mod_cast h












theorem emodTime_le {x : ℤ} {p U : ℕ} (hx : |x| ≤ (U : ℤ)) :
    emodTime x.natAbs p ≤ residueBudget U := by
  have hU : x.natAbs ≤ U := by simpa only [← Int.natCast_natAbs, Nat.cast_le] using hx
  have h := emodRounds_le (M := p) hU
  unfold emodTime residueBudget
  omega





















































































end ThreeSum.LightResidues

end

section


/-! # Independent cardinality-and-bucket trimming test -/

namespace ThreeSum.LightSourceFlagTest

open Light




theorem flag_le (card required count cap : ℕ) : flag card required count cap ≤ 1 := by
  unfold flag
  split <;> omega













variable {lim : Limits} {P : Program} {d : ℕ}






















end ThreeSum.LightSourceFlagTest

end

section


/-!
# Counting and hashing one physical block row

A single scan of the Boolean row constructs its cardinality and both raw
one-hot hashes. The two orientations are accumulated independently from the
stored unscaled map rows. All arithmetic is explicitly word bounded.
-/

namespace ThreeSum.LightSourceRowScan

open Light Finset
open scoped BigOperators

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
















theorem count_le {L j : ℕ} (bits : ℕ → ℕ) (hb : ∀ i < L, bits i ≤ 1) (hj : j ≤ L) :
    count bits j ≤ j := by
  unfold count
  calc
    _ ≤ ∑ _i ∈ range j, (1 : ℕ) :=
      Finset.sum_le_sum (fun i hi => hb i ((mem_range.mp hi).trans_le hj))
    _ = j := by simp

theorem hash_le {L j U : ℕ} (bits w0 w1 : ℕ → ℕ)
    (h0 : ∀ i < L, w0 i ≤ U) (h1 : ∀ i < L, w1 i ≤ U) (hj : j ≤ L) :
    hash bits w0 w1 j ≤ j*U := by
  unfold hash
  calc
    _ ≤ ∑ _i ∈ range j, U := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := (mem_range.mp hi).trans_le hj
      split
      · exact h1 i hi'
      · exact h0 i hi'
    _ = j*U := by simp
























variable {lim : Limits} {P : Program} {d : ℕ}






































































































end ThreeSum.LightSourceRowScan

end

section


/-!
# Constructing both independent trimming flags for one block row

The program counts and hashes the actual Boolean row, reduces both local
hashes, reads the selected map's retained bucket tables, and independently
tests the two endpoint buckets. The cardinality test is performed for both
orientations, with no disjoint-pair or shared trimming assumption.
-/

namespace ThreeSum.LightSourceRowFlag

open Light

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000





theorem flag_le (L h p cap : ℕ) (bits w0 w1 hist : ℕ → ℕ) :
    flag L h p cap bits w0 w1 hist ≤ 1 := LightSourceFlagTest.flag_le ..





















variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets_sourceProof {pMain pRow pEmod pFlag : ℕ}
    (hmain : P[pMain]? = some (body pRow pEmod pFlag))
    (hrow : P[pRow]? = some LightSourceRowScan.body)
    (hem : P[pEmod]? = some emodBody)
    (hflag : P[pFlag]? = some LightSourceFlagTest.body)
    {μ : ℕ → ℤ} {src src0 src1 L h histL histR p cap dst work U V : ℕ}
    (bits w0 w1 leftCount rightCount : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth) (hp : 0 < p) (hh : h ≤ L)
    (hsrc : src+L ≤ work) (hsrc0 : src0+L ≤ work) (hsrc1 : src1+L ≤ work)
    (hleft : histL+p ≤ work) (hright : histR+p ≤ work) (hdst : dst+2 ≤ work)
    (hspace : space work L U ≤ lim.space) (hword : (word L p U V cap : ℤ) ≤ lim.word)
    (hbits : ∀ i < L, μ (src+i) = (bits i : ℤ))
    (hread0 : ∀ i < L, μ (src0+i) = (w0 i : ℤ))
    (hread1 : ∀ i < L, μ (src1+i) = (w1 i : ℤ))
    (hbitBound : ∀ i < L, bits i ≤ 1)
    (hbound0 : ∀ i < L, w0 i ≤ U) (hbound1 : ∀ i < L, w1 i ≤ U)
    (hcountL : ∀ r < p, μ (histL+r) = (leftCount r : ℤ))
    (hcountR : ∀ r < p, μ (histR+r) = (rightCount r : ℤ))
    (hcountBoundL : ∀ r < p, leftCount r ≤ V)
    (hcountBoundR : ∀ r < p, rightCount r ≤ V) :
    Meets lim P pMain d [src,src0,src1,L,h,histL,histR,p,cap,dst,work] μ (time L U)
      (fun _ ν => ν dst = (flag L h p cap bits w0 w1 leftCount : ℤ) ∧
        ν (dst+1) = (flag L h p cap bits w1 w0 rightCount : ℤ) ∧
        KeptBut μ ν work dst 2) := by
  have hsp : work+3+(Nat.log 2 (L*U+1)+2) ≤ lim.space := hspace
  have hbudget (x : ℕ) (hx : x ≤ word L p U V cap) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hrowWord := hbudget (LightSourceRowScan.word L U) (by unfold word; omega)
  have hemWord : (4*(L*U : ℕ)+4*p+16 : ℤ) ≤ lim.word := by
    have hh := hbudget (4*(L*U)+4*p+16) (by unfold word; omega)
    exact_mod_cast hh
  have hpre : Emod.Pre lim p (L*U) (work+3) := ⟨hp,hw,hemWord,hsp⟩
  have hcBound := LightSourceRowScan.count_le bits hbitBound (j := L) le_rfl
  have hlBound := LightSourceRowScan.hash_le bits w0 w1 hbound0 hbound1 (j := L) le_rfl
  have hrBound := LightSourceRowScan.hash_le bits w1 w0 hbound1 hbound0 (j := L) le_rfl
  have hlAbs : |(LightSourceRowScan.hash bits w0 w1 L : ℤ)| ≤ ((L*U : ℕ) : ℤ) := by
    rw [Int.abs_natCast]
    exact Int.ofNat_le.mpr hlBound
  have hrAbs : |(LightSourceRowScan.hash bits w1 w0 L : ℤ)| ≤ ((L*U : ℕ) : ℤ) := by
    rw [Int.abs_natCast]
    exact Int.ofNat_le.mpr hrBound
  have htimeL := LightResidues.emodTime_le (p := p) hlAbs
  have htimeR := LightResidues.emodTime_le (p := p) hrAbs
  unfold emodTime LightResidues.residueBudget at htimeL htimeR
  simp only [Int.natAbs_natCast] at htimeL htimeR
  have hlog : Nat.log 2 (1+L*U) = Nat.log 2 (L*U+1) := by rw [Nat.add_comm]
  have hlLt := LightResidues.residue_lt hp 1 (LightSourceRowScan.hash bits w0 w1 L : ℤ)
  have hrLt := LightResidues.residue_lt hp 1 (LightSourceRowScan.hash bits w1 w0 L : ℤ)
  have hlCast := LightResidues.residue_cast hp 1 (LightSourceRowScan.hash bits w0 w1 L : ℤ)
  have hrCast := LightResidues.residue_cast hp 1 (LightSourceRowScan.hash bits w1 w0 L : ℤ)
  simp only [one_mul] at hlCast hrCast
  apply Meets.of_body hmain
  unfold body time
  have hr := LightSourceRowScan.meets (d := d+1) (μ := μ) (src := src)
    (src0 := src0) (src1 := src1) (L := L) (dst := work) (U := U)
    hrow bits w0 w1 hw (by omega) (by omega) (by omega) (by omega) hrowWord
    hbits hread0 hread1 hbitBound hbound0 hbound1
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
      | refine Light.Ends.callToThen (hr _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hr ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightSourceRowScan.time, LightResidues.residueBudget,
                LightSourceFlagTest.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightSourceRowScan.time, LightResidues.residueBudget,
                LightSourceFlagTest.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, LightSourceRowScan.time,
                LightResidues.residueBudget, LightSourceFlagTest.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro q ν₁ ⟨cardRead, leftRead, rightRead, kept₁⟩);
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
    (first
      |
        refine
          Light.Ends.callToThen
            ((emod_meets (x := (LightSourceRowScan.hash bits w0 w1 L : ℤ)) hem
                hpre hlAbs)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (emod_meets (x := (LightSourceRowScan.hash bits w0 w1 L : ℤ)) hem hpre
              hlAbs)
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                leftRead, LightSourceRowScan.time, LightResidues.residueBudget,
                LightSourceFlagTest.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [leftRead, LightSourceRowScan.time, LightResidues.residueBudget,
                LightSourceFlagTest.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, leftRead,
                LightSourceRowScan.time, LightResidues.residueBudget,
                LightSourceFlagTest.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro l ν₂ ⟨lResult, kept₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  rw [← hlCast] at lResult
  subst l
  have rightRead₂ : ν₂ (work+2) = (LightSourceRowScan.hash bits w1 w0 L : ℤ) :=
    (kept₂ _ (by omega)).trans rightRead
  have rightAddr : ((work : ℤ)+2).toNat = work+2 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using (Int.toNat_natCast (work+2))
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
            ((emod_meets (x := (LightSourceRowScan.hash bits w1 w0 L : ℤ)) hem
                hpre hrAbs)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (emod_meets (x := (LightSourceRowScan.hash bits w1 w0 L : ℤ)) hem hpre
              hrAbs)
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                rightRead₂, rightAddr, LightSourceRowScan.time,
                LightResidues.residueBudget, LightSourceFlagTest.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [rightRead₂, rightAddr, LightSourceRowScan.time,
                LightResidues.residueBudget, LightSourceFlagTest.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, rightRead₂, rightAddr,
                LightSourceRowScan.time, LightResidues.residueBudget,
                LightSourceFlagTest.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro r ν₃ ⟨rResult, kept₃⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  rw [← hrCast] at rResult
  subst r
  have cardRead₃ : ν₃ work = (LightSourceRowScan.count bits L : ℤ) :=
    (kept₃ _ (by omega)).trans ((kept₂ _ (by omega)).trans cardRead)
  have countLRead : ν₃ (histL+LightResidues.residue p 1
      (LightSourceRowScan.hash bits w0 w1 L : ℤ)) =
      (leftCount (LightResidues.residue p 1 (LightSourceRowScan.hash bits w0 w1 L : ℤ)) : ℤ) :=
    (kept₃ _ (by omega)).trans ((kept₂ _ (by omega)).trans
      ((kept₁ _ (Or.inl (by omega))).trans (hcountL _ hlLt)))
  have countRRead : ν₃ (histR+LightResidues.residue p 1
      (LightSourceRowScan.hash bits w1 w0 L : ℤ)) =
      (rightCount (LightResidues.residue p 1 (LightSourceRowScan.hash bits w1 w0 L : ℤ)) : ℤ) :=
    (kept₃ _ (by omega)).trans ((kept₂ _ (by omega)).trans
      ((kept₁ _ (Or.inl (by omega))).trans (hcountR _ hrLt)))
  have hflagWordL := hbudget (LightSourceRowScan.count bits L+h+
    leftCount (LightResidues.residue p 1 (LightSourceRowScan.hash bits w0 w1 L : ℤ))+cap+2)
    (by have := hcountBoundL _ hlLt; unfold word; omega)
  have hflagWordR := hbudget (LightSourceRowScan.count bits L+h+
    rightCount (LightResidues.residue p 1 (LightSourceRowScan.hash bits w1 w0 L : ℤ))+cap+2)
    (by have := hcountBoundR _ hrLt; unfold word; omega)
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
            ((LightSourceFlagTest.meets (d := d + 1) hflag ν₃ hflagWordL) _
              (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (LightSourceFlagTest.meets (d := d + 1) hflag ν₃ hflagWordL) ?_ ?_ ?_
            ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                cardRead₃, countLRead, LightSourceRowScan.time,
                LightResidues.residueBudget, LightSourceFlagTest.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [cardRead₃, countLRead, LightSourceRowScan.time,
                LightResidues.residueBudget, LightSourceFlagTest.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, cardRead₃, countLRead,
                LightSourceRowScan.time, LightResidues.residueBudget,
                LightSourceFlagTest.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro fl ν₄ ⟨flResult, hmem₄⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  subst ν₄
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
            ((LightSourceFlagTest.meets (d := d + 1) hflag ν₃ hflagWordR) _
              (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (LightSourceFlagTest.meets (d := d + 1) hflag ν₃ hflagWordR) ?_ ?_ ?_
            ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                cardRead₃, countRRead, LightSourceRowScan.time,
                LightResidues.residueBudget, LightSourceFlagTest.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [cardRead₃, countRRead, LightSourceRowScan.time,
                LightResidues.residueBudget, LightSourceFlagTest.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, cardRead₃, countRRead,
                LightSourceRowScan.time, LightResidues.residueBudget,
                LightSourceFlagTest.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro fr ν₅ ⟨frResult, hmem₅⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  subst ν₅
  have flEq : fl = (flag L h p cap bits w0 w1 leftCount : ℤ) := flResult
  have frEq : fr = (flag L h p cap bits w1 w0 rightCount : ℤ) := frResult
  have flBound := flag_le L h p cap bits w0 w1 leftCount
  have frBound := flag_le L h p cap bits w1 w0 rightCount
  have h1 := hbudget 1 (by unfold word; omega)
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
        Light.Ends.storeToThen dst (flag L h p cap bits w0 w1 leftCount : ℕ) ?_ ?_
          ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, flEq,
                LightSourceRowScan.time, LightResidues.residueBudget,
                LightSourceFlagTest.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [flEq, LightSourceRowScan.time, LightResidues.residueBudget,
                LightSourceFlagTest.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, flEq,
                LightSourceRowScan.time, LightResidues.residueBudget,
                LightSourceFlagTest.time] <;>
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
        Light.Ends.storeToThen (dst + 1)
          (flag L h p cap bits w1 w0 rightCount : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, frEq,
                LightSourceRowScan.time, LightResidues.residueBudget,
                LightSourceFlagTest.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [frEq, LightSourceRowScan.time, LightResidues.residueBudget,
                LightSourceFlagTest.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, frEq,
                LightSourceRowScan.time, LightResidues.residueBudget,
                LightSourceFlagTest.time] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  refine ⟨by simp,by simp,?_⟩
  intro a ⟨ha,hout⟩
  simp only [Function.update_of_ne (show a ≠ dst+1 by omega),
    Function.update_of_ne (show a ≠ dst by omega)]
  exact (kept₃ a (by omega)).trans ((kept₂ a (by omega)).trans (kept₁ a (Or.inl ha)))









end ThreeSum.LightSourceRowFlag

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain pRow pEmod pFlag : Nat},
  @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMain)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightSourceRowFlag.body pRow pEmod pFlag)) →
    @Eq.{1} (Option.{0} Light.Stmt)
        (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
          (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
          (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pRow)
        (@Option.some.{0} Light.Stmt ThreeSum.LightSourceRowScan.body) →
      @Eq.{1} (Option.{0} Light.Stmt)
          (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
            (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
            (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pEmod)
          (@Option.some.{0} Light.Stmt Light.emodBody) →
        @Eq.{1} (Option.{0} Light.Stmt)
            (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
              (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
              (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pFlag)
            (@Option.some.{0} Light.Stmt ThreeSum.LightSourceFlagTest.body) →
          ∀ {μ : Nat → Int} {src src0 src1 L h histL histR p cap dst work U V : Nat}
            (bits w0 w1 leftCount rightCount : Nat → Nat),
            @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
              @LT.lt.{0} Nat instLTNat d lim.depth →
                @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p →
                  @LE.le.{0} Nat instLENat h L →
                    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src L)
                        work →
                      @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src0 L)
                          work →
                        @LE.le.{0} Nat instLENat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src1 L) work →
                          @LE.le.{0} Nat instLENat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histL p) work →
                            @LE.le.{0} Nat instLENat
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histR p) work →
                              @LE.le.{0} Nat instLENat
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  work →
                                @LE.le.{0} Nat instLENat (ThreeSum.LightSourceRowFlag.space work L U) lim.space →
                                  @LE.le.{0} Int Int.instLEInt
                                      (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightSourceRowFlag.word L p U V cap))
                                      lim.word →
                                    (∀ (i : Nat),
                                        @LT.lt.{0} Nat instLTNat i L →
                                          @Eq.{1} Int
                                            (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src i))
                                            (@Nat.cast.{0} Int instNatCastInt (bits i))) →
                                      (∀ (i : Nat),
                                          @LT.lt.{0} Nat instLTNat i L →
                                            @Eq.{1} Int
                                              (μ
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src0
                                                  i))
                                              (@Nat.cast.{0} Int instNatCastInt (w0 i))) →
                                        (∀ (i : Nat),
                                            @LT.lt.{0} Nat instLTNat i L →
                                              @Eq.{1} Int
                                                (μ
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src1
                                                    i))
                                                (@Nat.cast.{0} Int instNatCastInt (w1 i))) →
                                          (∀ (i : Nat),
                                              @LT.lt.{0} Nat instLTNat i L →
                                                @LE.le.{0} Nat instLENat (bits i)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                            (∀ (i : Nat),
                                                @LT.lt.{0} Nat instLTNat i L → @LE.le.{0} Nat instLENat (w0 i) U) →
                                              (∀ (i : Nat),
                                                  @LT.lt.{0} Nat instLTNat i L → @LE.le.{0} Nat instLENat (w1 i) U) →
                                                (∀ (r : Nat),
                                                    @LT.lt.{0} Nat instLTNat r p →
                                                      @Eq.{1} Int
                                                        (μ
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) histL r))
                                                        (@Nat.cast.{0} Int instNatCastInt (leftCount r))) →
                                                  (∀ (r : Nat),
                                                      @LT.lt.{0} Nat instLTNat r p →
                                                        @Eq.{1} Int
                                                          (μ
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat) histR r))
                                                          (@Nat.cast.{0} Int instNatCastInt (rightCount r))) →
                                                    (∀ (r : Nat),
                                                        @LT.lt.{0} Nat instLTNat r p →
                                                          @LE.le.{0} Nat instLENat (leftCount r) V) →
                                                      (∀ (r : Nat),
                                                          @LT.lt.{0} Nat instLTNat r p →
                                                            @LE.le.{0} Nat instLENat (rightCount r) V) →
                                                        Light.Meets lim P pMain d
                                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
                                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src0)
                                                              (@List.cons.{0} Int
                                                                (@Nat.cast.{0} Int instNatCastInt src1)
                                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
                                                                  (@List.cons.{0} Int
                                                                    (@Nat.cast.{0} Int instNatCastInt h)
                                                                    (@List.cons.{0} Int
                                                                      (@Nat.cast.{0} Int instNatCastInt histL)
                                                                      (@List.cons.{0} Int
                                                                        (@Nat.cast.{0} Int instNatCastInt histR)
                                                                        (@List.cons.{0} Int
                                                                          (@Nat.cast.{0} Int instNatCastInt p)
                                                                          (@List.cons.{0} Int
                                                                            (@Nat.cast.{0} Int instNatCastInt cap)
                                                                            (@List.cons.{0} Int
                                                                              (@Nat.cast.{0} Int instNatCastInt dst)
                                                                              (@List.cons.{0} Int
                                                                                (@Nat.cast.{0} Int instNatCastInt work)
                                                                                (@List.nil.{0} Int))))))))))))
                                                          μ (ThreeSum.LightSourceRowFlag.time L U)
                                                          fun (x : Int) (ν : Nat → Int) =>
                                                          And
                                                            (@Eq.{1} Int (ν dst)
                                                              (@Nat.cast.{0} Int instNatCastInt
                                                                (ThreeSum.LightSourceRowFlag.flag L h p cap bits w0 w1
                                                                  leftCount)))
                                                            (And
                                                              (@Eq.{1} Int
                                                                (ν
                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                    (@instHAdd.{0} Nat instAddNat) dst
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                      (instOfNatNat (nat_lit 1)))))
                                                                (@Nat.cast.{0} Int instNatCastInt
                                                                  (ThreeSum.LightSourceRowFlag.flag L h p cap bits w1 w0
                                                                    rightCount)))
                                                              (Light.KeptBut μ ν work dst
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                  (instOfNatNat (nat_lit 2))))) := by
  exact @ThreeSum.LightSourceRowFlag.meets_sourceProof

#print axioms solution
