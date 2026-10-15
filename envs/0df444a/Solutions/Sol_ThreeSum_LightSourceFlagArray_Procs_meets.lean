-- Prove2me | solution 1 for ThreeSum.LightSourceFlagArray.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:33:22.303236+00:00
-- url     : https://prove2.me/submissions/e4423631-0942-43e3-8612-68f40940a909

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
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
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
import Mathlib.Algebra.Order.Ring.Nat
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
import Mathlib.Tactic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_Light_Ends_for
import Theorems.Thm_ThreeSum_LightSourceMaskFlags_Procs_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.SourceFlagProduct
end ThreeSum.SourceFlagProduct

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



























































































































end ThreeSum.LightSourceRowFlag

end

section


/-! # Conjunction represented by the product of independently computed flags -/

namespace ThreeSum.SourceFlagProduct

open Finset
open scoped BigOperators



@[simp] theorem product_zero (flag : ℕ → ℕ) : product flag 0=1 := by simp [product]

theorem product_succ (flag : ℕ → ℕ) (n : ℕ) :
    product flag (n+1)=product flag n*flag n := Finset.prod_range_succ _ _

theorem product_le {n j : ℕ} (flag : ℕ → ℕ)
    (hflag : ∀ i < n, flag i ≤ 1) (hj : j ≤ n) : product flag j ≤ 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [product_succ]
    exact (Nat.mul_le_mul (ih (by omega)) (hflag j (by omega))).trans (by decide)



























end ThreeSum.SourceFlagProduct

end

section


/-!
# Independent endpoint trimming across all selected blocks

The loop reads each occurrence index and its exact selected-candidate index,
then calls the concrete row flag constructor on the corresponding map and
retained bucket tables. The product of the independent Boolean flags is
written in each orientation. Input Boolean rows and tables are preserved.
-/

namespace ThreeSum.LightSourceTrim

open Light SourceFlagProduct

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000






theorem rowFlag_le (L h p cap : ℕ) (sel candidate bits : ℕ → ℕ)
    (w0 w1 counts : ℕ → ℕ → ℕ) (j : ℕ) :
    rowFlag L h p cap sel candidate bits w0 w1 counts j ≤ 1 :=
  LightSourceRowFlag.flag_le ..













































variable {lim : Limits} {P : Program} {d : ℕ}











































































































































































end ThreeSum.LightSourceTrim

end

section


/-!
# Constructing contiguous arrays of independent source flags

The actual loop reads the already enumerated global masks. For each one it
constructs both independent flags from selected maps and retained bucket
counts, then writes the two orientations in separate adjacent arrays. Powers,
Boolean coordinates and local arithmetic scratch are reused across masks.
-/

namespace ThreeSum.LightSourceFlagArray

open Light SourceFlagProduct

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000






theorem flag_le (J L h p cap : ℕ) (sel candidate : ℕ → ℕ)
    (w0 w1 counts : ℕ → ℕ → ℕ) (mask : ℕ) :
    flag J L h p cap sel candidate w0 w1 counts mask ≤ 1 :=
  product_le _ (fun _ _ => LightSourceTrim.rowFlag_le ..) le_rfl


























variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets_sourceProof {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {J L h p cap occ maps candidates histL histR masks n dst bitBase rowOut work U V M K : ℕ}
    (sel candidate mask : ℕ → ℕ) (w0 w1 leftCount rightCount : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*L+4 ≤ lim.depth)
    (hp : 0 < p) (hh : h ≤ L)
    (hocc : occ+J ≤ dst) (hmaps : maps+2*L*M ≤ dst)
    (hcandidates : candidates+M ≤ dst)
    (hleft : histL+K*p ≤ dst) (hright : histR+K*p ≤ dst)
    (hmasks : masks+n ≤ dst) (hdst : dst+2*n+2 ≤ bitBase)
    (hbits : bitBase+J*L ≤ rowOut) (hrowOut : rowOut+2 ≤ work)
    (hspace : LightSourceMaskFlags.space work J L U ≤ lim.space)
    (hword : (LightSourceMaskFlags.word J L p U V cap : ℤ) ≤ lim.word)
    (hsel : ∀ j < J, sel j < M) (hcandidate : ∀ s < M, candidate s < K)
    (hoccRead : ∀ j < J, μ (occ+j) = (sel j : ℤ))
    (hcandidateRead : ∀ s < M, μ (candidates+s) = (candidate s : ℤ))
    (hread0 : ∀ s < M, ∀ a < L, μ (maps+2*L*s+a) = (w0 s a : ℤ))
    (hread1 : ∀ s < M, ∀ a < L, μ (maps+2*L*s+L+a) = (w1 s a : ℤ))
    (hbound0 : ∀ s < M, ∀ a < L, w0 s a ≤ U)
    (hbound1 : ∀ s < M, ∀ a < L, w1 s a ≤ U)
    (hcountL : ∀ k < K, ∀ r < p, μ (histL+k*p+r) = (leftCount k r : ℤ))
    (hcountR : ∀ k < K, ∀ r < p, μ (histR+k*p+r) = (rightCount k r : ℤ))
    (hcountBoundL : ∀ k < K, ∀ r < p, leftCount k r ≤ V)
    (hcountBoundR : ∀ k < K, ∀ r < p, rightCount k r ≤ V)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskBound : ∀ i < n, mask i < 2^(J*L)) :
    Meets lim P pMain d
      [J,L,h,p,cap,occ,maps,candidates,histL,histR,masks,n,dst,bitBase,rowOut,work]
      μ (time n J L U) (fun _ ν =>
        (∀ i < n, ν (dst+i) = (flag J L h p cap sel candidate w0 w1 leftCount (mask i) : ℤ)) ∧
        (∀ i < n, ν (dst+n+i) = (flag J L h p cap sel candidate w1 w0 rightCount (mask i) : ℤ)) ∧
        KeptBut μ ν bitBase dst (2*n+2)) := by
  have hspace' : work ≤ lim.space := by
    unfold LightSourceMaskFlags.space at hspace
    omega
  have hone : (1 : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (show 1 ≤ lim.space by omega)).trans hw
  apply Meets.of_body S.main
  unfold body time
  refine Ends.for (Inv μ J L h p cap occ maps candidates histL histR masks n dst bitBase rowOut work
    sel candidate mask w0 w1 leftCount rightCount) n
    (LightSourceMaskFlags.time J L U+192) ?start ?round ?done ?bound
  case start =>
    refine ⟨0,μ,?_,?_,?_,fun _ _ => rfl⟩
    · exact congrArg (fun loc => (⟨loc,μ⟩ : State))
        ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro j hj; omega
    · intro j hj; omega
  case round =>
    rintro i _ hi _ ⟨r,ν,rfl,leftWritten,rightWritten,kept⟩
    have hkeep : Kept μ ν dst := by
      intro a ha
      exact kept a ⟨by omega,Or.inl ha⟩
    have hocc' : ∀ j < J, ν (occ+j) = (sel j : ℤ) := by
      intro j hj
      exact (hkeep _ (by omega)).trans (hoccRead j hj)
    have hcan' : ∀ s < M, ν (candidates+s) = (candidate s : ℤ) := by
      intro s hs
      exact (hkeep _ (by omega)).trans (hcandidateRead s hs)
    have hread0' : ∀ s < M, ∀ a < L, ν (maps+2*L*s+a) = (w0 s a : ℤ) := by
      intro s hs a ha
      have he := Nat.mul_le_mul_left (2*L) (show s+1 ≤ M by omega)
      exact (hkeep _ (by nlinarith)).trans (hread0 s hs a ha)
    have hread1' : ∀ s < M, ∀ a < L, ν (maps+2*L*s+L+a) = (w1 s a : ℤ) := by
      intro s hs a ha
      have he := Nat.mul_le_mul_left (2*L) (show s+1 ≤ M by omega)
      exact (hkeep _ (by nlinarith)).trans (hread1 s hs a ha)
    have hcountL' : ∀ k < K, ∀ r < p, ν (histL+k*p+r) = (leftCount k r : ℤ) := by
      intro k hk r hr
      have he := Nat.mul_le_mul_right p (show k+1 ≤ K by omega)
      exact (hkeep _ (by nlinarith)).trans (hcountL k hk r hr)
    have hcountR' : ∀ k < K, ∀ r < p, ν (histR+k*p+r) = (rightCount k r : ℤ) := by
      intro k hk r hr
      have he := Nat.mul_le_mul_right p (show k+1 ≤ K by omega)
      exact (hkeep _ (by nlinarith)).trans (hcountR k hk r hr)
    have hmask : ν (masks+i) = (mask i : ℤ) :=
      (hkeep _ (by omega)).trans (hmaskRead i hi)
    have hrun := S.flagProcs.meets (d := d+1) (μ := ν)
      (J := J) (L := L) (h := h) (p := p) (cap := cap) (occ := occ) (maps := maps)
      (candidates := candidates) (histL := histL) (histR := histR) (mask := mask i)
      (dst := dst+2*n) (bitBase := bitBase) (rowOut := rowOut) (work := work)
      (U := U) (V := V) (M := M) (K := K)
      sel candidate w0 w1 leftCount rightCount hw (by omega) hp hh
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hbits hrowOut hspace hword
      (hmaskBound i hi) hsel hcandidate hocc' hcan' hread0' hread1' hbound0 hbound1
      hcountL' hcountR' hcountBoundL hcountBoundR
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
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hmask,
                  LightSourceMaskFlags.time, LightMaskBits.time,
                  LightMaskErase.time, LightSourceTrim.time,
                  LightSourceRowFlag.time, LightSourceRowScan.time,
                  LightResidues.residueBudget, LightSourceFlagTest.time]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hmask, LightSourceMaskFlags.time, LightMaskBits.time,
                  LightMaskErase.time, LightSourceTrim.time,
                  LightSourceRowFlag.time, LightSourceRowScan.time,
                  LightResidues.residueBudget, LightSourceFlagTest.time] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 => omega);
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hmask,
                  LightSourceMaskFlags.time, LightMaskBits.time,
                  LightMaskErase.time, LightSourceTrim.time,
                  LightSourceRowFlag.time, LightSourceRowScan.time,
                  LightResidues.residueBudget, LightSourceFlagTest.time] <;>
                omega)));
      (on_goal -1 =>
          ((rintro q ν₁ ⟨left, right, kept₁⟩);
            (try with_unfolding_none refine Light.Ends.skip ?_)))
    have hl : ν₁ (dst+2*n) = (flag J L h p cap sel candidate w0 w1 leftCount (mask i) : ℤ) := left
    have hr : ν₁ (dst+2*n+1) = (flag J L h p cap sel candidate w1 w0 rightCount (mask i) : ℤ) := right
    have hlB := flag_le J L h p cap sel candidate w0 w1 leftCount (mask i)
    have hrB := flag_le J L h p cap sel candidate w1 w0 rightCount (mask i)
    have haddr : ((dst : ℤ)+2*(n : ℤ)).toNat = dst+2*n := by
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using Int.toNat_natCast (dst+2*n)
    have haddrR : ((dst : ℤ)+2*(n : ℤ)+1).toNat = dst+2*n+1 := by
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using Int.toNat_natCast (dst+2*n+1)
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
          Light.Ends.storeToThen (dst + i)
            (flag J L h p cap sel candidate w0 w1 leftCount (mask i) : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hl,
                  haddr, LightSourceMaskFlags.time, LightMaskBits.time,
                  LightMaskErase.time, LightSourceTrim.time,
                  LightSourceRowFlag.time, LightSourceRowScan.time,
                  LightResidues.residueBudget, LightSourceFlagTest.time]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hl, haddr, LightSourceMaskFlags.time, LightMaskBits.time,
                  LightMaskErase.time, LightSourceTrim.time,
                  LightSourceRowFlag.time, LightSourceRowScan.time,
                  LightResidues.residueBudget, LightSourceFlagTest.time] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hl, haddr,
                  LightSourceMaskFlags.time, LightMaskBits.time,
                  LightMaskErase.time, LightSourceTrim.time,
                  LightSourceRowFlag.time, LightSourceRowScan.time,
                  LightResidues.residueBudget, LightSourceFlagTest.time] <;>
                omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    have hr' : Function.update ν₁ (dst+i)
        (flag J L h p cap sel candidate w0 w1 leftCount (mask i) : ℤ) (dst+2*n+1) =
        (flag J L h p cap sel candidate w1 w0 rightCount (mask i) : ℤ) := by
      rw [Function.update_of_ne (by omega)]
      exact hr
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
          Light.Ends.storeToThen (dst + n + i)
            (flag J L h p cap sel candidate w1 w0 rightCount (mask i) : ℕ) ?_ ?_
            ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hr',
                  haddrR, LightSourceMaskFlags.time, LightMaskBits.time,
                  LightMaskErase.time, LightSourceTrim.time,
                  LightSourceRowFlag.time, LightSourceRowScan.time,
                  LightResidues.residueBudget, LightSourceFlagTest.time]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hr', haddrR, LightSourceMaskFlags.time, LightMaskBits.time,
                  LightMaskErase.time, LightSourceTrim.time,
                  LightSourceRowFlag.time, LightSourceRowScan.time,
                  LightResidues.residueBudget, LightSourceFlagTest.time] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hr', haddrR,
                  LightSourceMaskFlags.time, LightMaskBits.time,
                  LightMaskErase.time, LightSourceTrim.time,
                  LightSourceRowFlag.time, LightSourceRowScan.time,
                  LightResidues.residueBudget, LightSourceFlagTest.time] <;>
                omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    refine ⟨by simp,q,Function.update
      (Function.update ν₁ (dst+i) (flag J L h p cap sel candidate w0 w1 leftCount (mask i) : ℤ))
      (dst+n+i) (flag J L h p cap sel candidate w1 w0 rightCount (mask i) : ℤ),
      by simp [update_frame_setLocal],?_,?_,?_⟩
    · intro j hj
      rw [Function.update_of_ne (by omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega)]
        exact (kept₁ _ ⟨by omega,Or.inl (by omega)⟩).trans (leftWritten j hj)
      · simp
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
        exact (kept₁ _ ⟨by omega,Or.inl (by omega)⟩).trans (rightWritten j hj)
      · simp
    · intro a ⟨ha,hout⟩
      rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
      exact (kept₁ a ⟨ha,by omega⟩).trans (kept a ⟨ha,hout⟩)
  case done =>
    rintro _ _ ⟨r,ν,rfl,left,right,kept⟩
    exact ⟨left,right,kept⟩
  case bound =>
    rintro i _ _ _ ⟨r,ν,rfl,_,_,_⟩
    simp
















end ThreeSum.LightSourceFlagArray

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (S : ThreeSum.LightSourceFlagArray.Procs P pMain)
  {μ : Nat → Int} {J L h p cap occ maps candidates histL histR masks n dst bitBase rowOut work U V M K : Nat}
  (sel candidate mask : Nat → Nat) (w0 w1 leftCount rightCount : Nat → Nat → Nat),
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J L))
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        lim.depth →
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p →
        @LE.le.{0} Nat instLENat h L →
          @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) occ J) dst →
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)
                    M))
                dst →
              @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) candidates M)
                  dst →
                @LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histL
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) K p))
                    dst →
                  @LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histR
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) K p))
                      dst →
                    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) masks n)
                        dst →
                      @LE.le.{0} Nat instLENat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          bitBase →
                        @LE.le.{0} Nat instLENat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bitBase
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J L))
                            rowOut →
                          @LE.le.{0} Nat instLENat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rowOut
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              work →
                            @LE.le.{0} Nat instLENat (ThreeSum.LightSourceMaskFlags.space work J L U) lim.space →
                              @LE.le.{0} Int Int.instLEInt
                                  (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightSourceMaskFlags.word J L p U V cap))
                                  lim.word →
                                (∀ (j : Nat), @LT.lt.{0} Nat instLTNat j J → @LT.lt.{0} Nat instLTNat (sel j) M) →
                                  (∀ (s : Nat),
                                      @LT.lt.{0} Nat instLTNat s M → @LT.lt.{0} Nat instLTNat (candidate s) K) →
                                    (∀ (j : Nat),
                                        @LT.lt.{0} Nat instLTNat j J →
                                          @Eq.{1} Int
                                            (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) occ j))
                                            (@Nat.cast.{0} Int instNatCastInt (sel j))) →
                                      (∀ (s : Nat),
                                          @LT.lt.{0} Nat instLTNat s M →
                                            @Eq.{1} Int
                                              (μ
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  candidates s))
                                              (@Nat.cast.{0} Int instNatCastInt (candidate s))) →
                                        (∀ (s : Nat),
                                            @LT.lt.{0} Nat instLTNat s M →
                                              ∀ (a : Nat),
                                                @LT.lt.{0} Nat instLTNat a L →
                                                  @Eq.{1} Int
                                                    (μ
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          maps
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              L)
                                                            s))
                                                        a))
                                                    (@Nat.cast.{0} Int instNatCastInt (w0 s a))) →
                                          (∀ (s : Nat),
                                              @LT.lt.{0} Nat instLTNat s M →
                                                ∀ (a : Nat),
                                                  @LT.lt.{0} Nat instLTNat a L →
                                                    @Eq.{1} Int
                                                      (μ
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat) maps
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                    (instOfNatNat (nat_lit 2)))
                                                                  L)
                                                                s))
                                                            L)
                                                          a))
                                                      (@Nat.cast.{0} Int instNatCastInt (w1 s a))) →
                                            (∀ (s : Nat),
                                                @LT.lt.{0} Nat instLTNat s M →
                                                  ∀ (a : Nat),
                                                    @LT.lt.{0} Nat instLTNat a L →
                                                      @LE.le.{0} Nat instLENat (w0 s a) U) →
                                              (∀ (s : Nat),
                                                  @LT.lt.{0} Nat instLTNat s M →
                                                    ∀ (a : Nat),
                                                      @LT.lt.{0} Nat instLTNat a L →
                                                        @LE.le.{0} Nat instLENat (w1 s a) U) →
                                                (∀ (k : Nat),
                                                    @LT.lt.{0} Nat instLTNat k K →
                                                      ∀ (r : Nat),
                                                        @LT.lt.{0} Nat instLTNat r p →
                                                          @Eq.{1} Int
                                                            (μ
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat) histL
                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                    (@instHMul.{0} Nat instMulNat) k p))
                                                                r))
                                                            (@Nat.cast.{0} Int instNatCastInt (leftCount k r))) →
                                                  (∀ (k : Nat),
                                                      @LT.lt.{0} Nat instLTNat k K →
                                                        ∀ (r : Nat),
                                                          @LT.lt.{0} Nat instLTNat r p →
                                                            @Eq.{1} Int
                                                              (μ
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat)
                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                    (@instHAdd.{0} Nat instAddNat) histR
                                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                      (@instHMul.{0} Nat instMulNat) k p))
                                                                  r))
                                                              (@Nat.cast.{0} Int instNatCastInt (rightCount k r))) →
                                                    (∀ (k : Nat),
                                                        @LT.lt.{0} Nat instLTNat k K →
                                                          ∀ (r : Nat),
                                                            @LT.lt.{0} Nat instLTNat r p →
                                                              @LE.le.{0} Nat instLENat (leftCount k r) V) →
                                                      (∀ (k : Nat),
                                                          @LT.lt.{0} Nat instLTNat k K →
                                                            ∀ (r : Nat),
                                                              @LT.lt.{0} Nat instLTNat r p →
                                                                @LE.le.{0} Nat instLENat (rightCount k r) V) →
                                                        (∀ (i : Nat),
                                                            @LT.lt.{0} Nat instLTNat i n →
                                                              @Eq.{1} Int
                                                                (μ
                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                    (@instHAdd.{0} Nat instAddNat) masks i))
                                                                (@Nat.cast.{0} Int instNatCastInt (mask i))) →
                                                          (∀ (i : Nat),
                                                              @LT.lt.{0} Nat instLTNat i n →
                                                                @LT.lt.{0} Nat instLTNat (mask i)
                                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                                    (@instHPow.{0, 0} Nat Nat
                                                                      (@NPow.toPow.{0} Nat
                                                                        (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                      (instOfNatNat (nat_lit 2)))
                                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                      (@instHMul.{0} Nat instMulNat) J L))) →
                                                            Light.Meets lim P pMain d
                                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt J)
                                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
                                                                  (@List.cons.{0} Int
                                                                    (@Nat.cast.{0} Int instNatCastInt h)
                                                                    (@List.cons.{0} Int
                                                                      (@Nat.cast.{0} Int instNatCastInt p)
                                                                      (@List.cons.{0} Int
                                                                        (@Nat.cast.{0} Int instNatCastInt cap)
                                                                        (@List.cons.{0} Int
                                                                          (@Nat.cast.{0} Int instNatCastInt occ)
                                                                          (@List.cons.{0} Int
                                                                            (@Nat.cast.{0} Int instNatCastInt maps)
                                                                            (@List.cons.{0} Int
                                                                              (@Nat.cast.{0} Int instNatCastInt
                                                                                candidates)
                                                                              (@List.cons.{0} Int
                                                                                (@Nat.cast.{0} Int instNatCastInt histL)
                                                                                (@List.cons.{0} Int
                                                                                  (@Nat.cast.{0} Int instNatCastInt
                                                                                    histR)
                                                                                  (@List.cons.{0} Int
                                                                                    (@Nat.cast.{0} Int instNatCastInt
                                                                                      masks)
                                                                                    (@List.cons.{0} Int
                                                                                      (@Nat.cast.{0} Int instNatCastInt
                                                                                        n)
                                                                                      (@List.cons.{0} Int
                                                                                        (@Nat.cast.{0} Int
                                                                                          instNatCastInt dst)
                                                                                        (@List.cons.{0} Int
                                                                                          (@Nat.cast.{0} Int
                                                                                            instNatCastInt bitBase)
                                                                                          (@List.cons.{0} Int
                                                                                            (@Nat.cast.{0} Int
                                                                                              instNatCastInt rowOut)
                                                                                            (@List.cons.{0} Int
                                                                                              (@Nat.cast.{0} Int
                                                                                                instNatCastInt work)
                                                                                              (@List.nil.{0}
                                                                                                Int)))))))))))))))))
                                                              μ (ThreeSum.LightSourceFlagArray.time n J L U)
                                                              fun (x : Int) (ν : Nat → Int) =>
                                                              And
                                                                (∀ (i : Nat),
                                                                  @LT.lt.{0} Nat instLTNat i n →
                                                                    @Eq.{1} Int
                                                                      (ν
                                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                          (@instHAdd.{0} Nat instAddNat) dst i))
                                                                      (@Nat.cast.{0} Int instNatCastInt
                                                                        (ThreeSum.LightSourceFlagArray.flag J L h p cap
                                                                          sel candidate w0 w1 leftCount (mask i))))
                                                                (And
                                                                  (∀ (i : Nat),
                                                                    @LT.lt.{0} Nat instLTNat i n →
                                                                      @Eq.{1} Int
                                                                        (ν
                                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                            (@instHAdd.{0} Nat instAddNat)
                                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                              (@instHAdd.{0} Nat instAddNat) dst n)
                                                                            i))
                                                                        (@Nat.cast.{0} Int instNatCastInt
                                                                          (ThreeSum.LightSourceFlagArray.flag J L h p
                                                                            cap sel candidate w1 w0 rightCount
                                                                            (mask i))))
                                                                  (Light.KeptBut μ ν bitBase dst
                                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                      (@instHAdd.{0} Nat instAddNat)
                                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                        (@instHMul.{0} Nat instMulNat)
                                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                          (instOfNatNat (nat_lit 2)))
                                                                        n)
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                        (instOfNatNat (nat_lit 2)))))) := by
  exact @ThreeSum.LightSourceFlagArray.Procs.meets_sourceProof

#print axioms solution
