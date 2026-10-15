-- Prove2me | solution 1 for ThreeSum.LightBlockCoefficients.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:45:37.632824+00:00
-- url     : https://prove2.me/submissions/6e9378ab-cd99-4e9a-ae65-981316ff009d

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
import Definitions.Def_ThreeSum1962Source_Bundle05
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
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
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
import Mathlib.Data.Nat.Cast.Order.Ring
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
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_Light_Ends_for
import Theorems.Thm_Light_Ends_pass
import Theorems.Thm_Light_powTable_ends


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace Light.PowTable
end Light.PowTable
namespace ThreeSum.LightArray
end ThreeSum.LightArray

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

/-- The case of a single cell. -/
theorem SameOn.cell (h : SameOn (· = b) μ μ') : μ' b = μ b := h b rfl




















/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}











/-- A cell that has been written. -/
theorem wrote_done {i : ℕ} (h : i < j) : wrote μ dst f j (dst + i) = f i := by
  unfold wrote
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

/-- A cell that has not been written (yet). -/
theorem wrote_rest {a : ℕ} (h : Outside dst j a) : wrote μ dst f j a = μ a := by
  unfold wrote
  rw [if_neg (by omega)]


























/-! ## The tactics -/









































end Light

end
end

section


/-!
# Costed array arithmetic in the benchmark's imperative language

These are actual `Light.Stmt` programs and `Light.Meets` execution proofs.
Their contracts count every expression evaluation and memory operation.
-/

namespace ThreeSum.LightArray

open Light

variable {lim : Limits} {P : Program} {d : ℕ}





theorem source_read {μ : ℕ → ℤ} {src dst n j : ℕ} {f : ℕ → ℤ}
    (h : SourceSafe src dst n) (hj : j < n) :
    wrote μ dst f j (src + j) = μ (src + j) := by
  rcases h with rfl | h
  · exact wrote_rest (by omega)
  · exact wrote_rest (by omega)
































































end ThreeSum.LightArray

end

section


/-! # A costed array scaling pass -/

namespace ThreeSum.LightScaleArray

open Light ThreeSum.LightArray

variable {lim : Limits} {P : Program} {d : ℕ}





theorem meets {p src dst n : ℕ} {c : ℤ} {μ : ℕ → ℤ}
    (hp : P[p]? = some body)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+n ≤ lim.space) (hdst : dst+n ≤ lim.space)
    (hsep : SourceSafe src dst n)
    (hword : ∀ i < n, |c*μ (src+i)| ≤ lim.word) :
    Meets lim P p d [src,dst,n,c] μ (time n)
      (fun _ μ' => (∀ i < n, μ' (dst+i) = c*μ (src+i)) ∧ SameOutside μ μ' dst n) := by
  refine .of_body hp (Ends.pass (fun i => c*μ (src+i))
    (fun i hi => ?_) ⟨fun i hi => wrote_done (f := fun i => c*μ (src+i)) hi,
      by ((try refine Light.SameOn.cell ?_); (intro apspMacro_24539_0 apspMacro_24539_1);
           (first
             |
               ((((repeat
                         (((with_reducible
                                 rename Light.SameOn _ _ _ => apspMacro_24539_2));
                           ((try
                                 have :=
                                   apspMacro_24539_2 apspMacro_24539_0 (by omega)));
                           (revert apspMacro_24539_2)));
                     (intros);
                     (try simp only [Function.update_apply, Light.wrote] at *)));
                 (omega))
             |
               ((simp [] at apspMacro_24539_1);
                 (((repeat
                         (((with_reducible
                                 rename Light.SameOn _ _ _ => apspMacro_24539_3));
                           ((try
                                 have :=
                                   apspMacro_24539_3 apspMacro_24539_0 (by omega)));
                           (revert apspMacro_24539_3)));
                     (intros);
                     (try simp only [Function.update_apply, Light.wrote] at *)));
                 (omega))
             |
               ((((repeat
                         (((with_reducible
                                 rename Light.SameOn _ _ _ => apspMacro_24539_4));
                           ((try
                                 have :=
                                   apspMacro_24539_4 apspMacro_24539_0 (by omega)));
                           (revert apspMacro_24539_4)));
                     (intros);
                     (try simp only [Function.update_apply, Light.wrote] at *)));
                 (fail
                     "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                               SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                               its condition K x does not follow from the hypotheses."))))⟩ hw hdst rfl rfl (hT := by first
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
                                                                                                                              | ((ring_nf); (omega)))))
  have hr := source_read (μ := μ) (f := fun i => c*μ (src+i)) hsep hi
  have hv := abs_le.mp (hword i hi)
  (((try have := Light.Std.space_le (by assumption)));
    ((try have := Light.Std.const_le (by assumption)));
    (simp [Light.Limits.Addr, abs_le, -abs_mul, hr] <;> omega))












end ThreeSum.LightScaleArray

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
# Constructing the positional one-hot coefficient arrays

The program reads one map occurrence per block. It copies both symbol rows
of that map and multiplies them by the block's radix power. The powers are
built internally. All original map and occurrence data are preserved.
-/

namespace ThreeSum.LightBlockCoefficients

open Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

variable {lim : Limits} {P : Program}

































theorem row_end_le {J L j : ℕ} (hj : j < J) : j*L+L ≤ J*L := by
  calc
    j*L+L = (j+1)*L := by ring
    _ ≤ J*L := Nat.mul_le_mul_right L (by omega)

theorem map_end_le {M L s : ℕ} (hs : s < M) : 2*L*s+L+L ≤ 2*L*M := by
  calc
    2*L*s+L+L = 2*L*(s+1) := by ring
    _ ≤ 2*L*M := Nat.mul_le_mul_left (2*L) (by omega)

theorem meets_sourceProof {pMain pPowers pScale : ℕ}
    (hmain : P[pMain]? = some (body pPowers pScale))
    (hpowers : P[pPowers]? = some powTableBody)
    (hscale : P[pScale]? = some LightScaleArray.body)
    {μ : ℕ → ℤ} {J L p occ maps dst0 dst1 work U M d : ℕ}
    (sel : ℕ → ℕ) (w0 w1 : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 1 ≤ p)
    (hocc : occ+J ≤ dst0) (hmaps : maps+2*L*M ≤ dst0)
    (hdst0 : dst0+J*L ≤ dst1) (hdst1 : dst1+J*L ≤ work)
    (hspace : work+(J+1) ≤ lim.space)
    (hword : (word J p U : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hsel : ∀ j < J, sel j < M)
    (hselRead : ∀ j < J, μ (occ+j) = (sel j : ℤ))
    (hread0 : ∀ s < M, ∀ i < L, μ (maps+2*L*s+i) = (w0 s i : ℤ))
    (hread1 : ∀ s < M, ∀ i < L, μ (maps+2*L*s+L+i) = (w1 s i : ℤ))
    (hbound0 : ∀ s < M, ∀ i < L, w0 s i ≤ U)
    (hbound1 : ∀ s < M, ∀ i < L, w1 s i ≤ U) :
    Meets lim P pMain d [J,L,p,occ,maps,dst0,dst1,work] μ (time J L)
      (fun _ ν => Rows ν dst0 dst1 L p sel w0 w1 J ∧
        Kept μ ν dst0 ∧ Powers ν work J p) := by
  have hpw : ∀ i ≤ J+1, ((p^i : ℕ) : ℤ) ≤ lim.word := by
    intro i hi
    have hh : p^i ≤ word J p U :=
      (Nat.pow_le_pow_right hp hi).trans (Nat.le_mul_of_pos_right _ (by omega))
    exact (by exact_mod_cast hh : ((p^i : ℕ) : ℤ) ≤ (word J p U : ℤ)).trans hword
  have hpb : (p : ℤ) ≤ lim.word := by simpa using hpw 1 (by omega)
  apply Meets.of_body hmain
  unfold body time
  have hpCall := powTable_meets (d := d+1) (μ := μ) (dst := work)
    (L := J+1) (b := p) hpowers hw hspace hpw
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
      | refine Light.Ends.callToThen (hpCall _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hpCall ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                powTableTime, roundTime, LightScaleArray.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [powTableTime, roundTime, LightScaleArray.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, powTableTime, roundTime,
                LightScaleArray.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro rPow ν₀ ⟨hpow, hkeep₀⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  refine Ends.for (Inv μ J L p occ maps dst0 dst1 work sel w0 w1)
    J (roundTime L) ?start ?round ?done ?bound (hT := by first
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
                                                               | ((ring_nf); (omega))))
  case start =>
    refine ⟨0,0,0,0,0,ν₀,?_,?_,?_,?_⟩
    · simp [update_frame_setLocal]
      change frame [(J : ℤ),L,p,occ,maps,dst0,dst1,work,0] =
        frame ([(J : ℤ),L,p,occ,maps,dst0,dst1,work,0] ++ [0,0,0,0,0])
      exact (frame_append_zeros _ 5).symm
    · intro a ha
      omega
    · intro a ha
      exact hkeep₀ a (Or.inl (by omega))
    · intro i hi
      have hh := hpow i (by simp; omega)
      simpa only [getElem_powList] using hh
  case round =>
    rintro j _ hj _ ⟨s,a,b,r0,r1,ν,rfl,hrows,hkept,hpows⟩
    have hs := hsel j hj
    have hme := map_end_le (L := L) hs
    have hre := row_end_le (L := L) hj
    have htwo : 2*L ≤ lim.space :=
      (Nat.le_mul_of_pos_right (2*L) (by omega : 0 < M)).trans (by omega)
    have hprod : 2*(L : ℤ)*(sel j : ℤ) ≤ lim.word := by
      have hh : 2*L*sel j ≤ lim.space := by omega
      exact (by exact_mod_cast hh : 2*(L : ℤ)*(sel j : ℤ) ≤ lim.space).trans hw
    have hprodNonneg : 0 ≤ 2*(L : ℤ)*(sel j : ℤ) := by positivity
    have haddrWord : (maps : ℤ)+2*(L : ℤ)*(sel j : ℤ) ≤ lim.word := by
      have hh : maps+2*L*sel j ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (maps : ℤ)+2*(L : ℤ)*(sel j : ℤ) ≤ lim.space).trans hw
    have haddrEndWord : (maps : ℤ)+2*(L : ℤ)*(sel j : ℤ)+(L : ℤ)+(L : ℤ) ≤ lim.word := by
      have hh : maps+2*L*sel j+L+L ≤ lim.space := by omega
      exact (by exact_mod_cast hh :
        (maps : ℤ)+2*(L : ℤ)*(sel j : ℤ)+(L : ℤ)+(L : ℤ) ≤ lim.space).trans hw
    have hrowProd : (j : ℤ)*(L : ℤ) ≤ lim.word := by
      have hh : j*L ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (j : ℤ)*(L : ℤ) ≤ lim.space).trans hw
    have hrowNonneg : 0 ≤ (j : ℤ)*(L : ℤ) := by positivity
    have hselection : ν (occ+j) = (sel j : ℤ) :=
      (hkept _ (by omega)).trans (hselRead j hj)
    have hpower := hpows j (by omega)
    have hread0' : ∀ i < L, ν (maps+2*L*sel j+i) = (w0 (sel j) i : ℤ) := by
      intro i hi
      exact (hkept _ (by omega)).trans (hread0 _ hs i hi)
    have hread1' : ∀ i < L, ν (maps+2*L*sel j+L+i) = (w1 (sel j) i : ℤ) := by
      intro i hi
      exact (hkept _ (by omega)).trans (hread1 _ hs i hi)
    have hv0 : ∀ i < L, |(p^j : ℕ)*ν (maps+2*L*sel j+i)| ≤ lim.word := by
      intro i hi
      rw [hread0' i hi]
      have hh : p^j*w0 (sel j) i ≤ word J p U :=
        Nat.mul_le_mul (Nat.pow_le_pow_right hp (by omega))
          ((hbound0 _ hs i hi).trans (Nat.le_succ U))
      have hz : (((p^j*w0 (sel j) i : ℕ) : ℤ)) ≤ lim.word :=
        (by exact_mod_cast hh : ((p^j*w0 (sel j) i : ℕ) : ℤ) ≤ (word J p U : ℤ)).trans hword
      simpa only [Nat.cast_mul,abs_mul,abs_of_nonneg (Int.natCast_nonneg _),Int.abs_natCast] using hz
    unfold roundBody roundTime
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (maps + 2 * L * sel j : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  hselection, LightScaleArray.time]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hselection, LightScaleArray.time] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hselection,
                  LightScaleArray.time] <;>
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
      (refine Light.Ends.setToThen (dst0 + j * L : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  LightScaleArray.time]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [LightScaleArray.time] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, LightScaleArray.time] <;>
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
      (refine Light.Ends.setToThen (dst1 + j * L : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  LightScaleArray.time]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [LightScaleArray.time] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, LightScaleArray.time] <;>
                omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    have hcall0 := LightScaleArray.meets (d := d+1) (src := maps+2*L*sel j)
      (dst := dst0+j*L) (n := L) (c := (p^j : ℕ)) hscale hw (by omega) (by omega)
      (Or.inr (Or.inl (by omega))) hv0
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
        | refine Light.Ends.callToThen (hcall0 _ (by omega)) ?_ ?_ ?_ ?_
        | refine Light.Ends.callToThen hcall0 ?_ ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hpower,
                  LightScaleArray.time]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hpower, LightScaleArray.time] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 => omega);
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hpower,
                  LightScaleArray.time] <;>
                omega)));
      (on_goal -1 =>
          ((rintro q0 ν₁ ⟨hout0, hkeep0⟩);
            (try with_unfolding_none refine Light.Ends.skip ?_)))
    have hpower₁ : ν₁ (work+j) = ((p^j : ℕ) : ℤ) :=
      (hkeep0 _ (Or.inr (by omega))).trans hpower
    have hread1'' : ∀ i < L, ν₁ (maps+2*L*sel j+L+i) = (w1 (sel j) i : ℤ) := by
      intro i hi
      exact (hkeep0 _ (Or.inl (by omega))).trans (hread1' i hi)
    have hv1 : ∀ i < L, |(p^j : ℕ)*ν₁ (maps+2*L*sel j+L+i)| ≤ lim.word := by
      intro i hi
      rw [hread1'' i hi]
      have hh : p^j*w1 (sel j) i ≤ word J p U :=
        Nat.mul_le_mul (Nat.pow_le_pow_right hp (by omega))
          ((hbound1 _ hs i hi).trans (Nat.le_succ U))
      have hz : (((p^j*w1 (sel j) i : ℕ) : ℤ)) ≤ lim.word :=
        (by exact_mod_cast hh : ((p^j*w1 (sel j) i : ℕ) : ℤ) ≤ (word J p U : ℤ)).trans hword
      simpa only [Nat.cast_mul,abs_mul,abs_of_nonneg (Int.natCast_nonneg _),Int.abs_natCast] using hz
    have hcall1 := LightScaleArray.meets (d := d+1) (src := maps+2*L*sel j+L)
      (dst := dst1+j*L) (n := L) (c := (p^j : ℕ)) hscale hw (by omega) (by omega)
      (Or.inr (Or.inl (by omega))) hv1
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
        | refine Light.Ends.callToThen (hcall1 _ (by omega)) ?_ ?_ ?_ ?_
        | refine Light.Ends.callToThen hcall1 ?_ ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hpower₁,
                  LightScaleArray.time]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hpower₁, LightScaleArray.time] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 => omega);
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hpower₁,
                  LightScaleArray.time] <;>
                omega)));
      (on_goal -1 =>
          ((rintro q1 ν₂ ⟨hout1, hkeep1⟩);
            (try with_unfolding_none refine Light.Ends.skip ?_)))
    refine ⟨by simp,((maps+2*L*sel j : ℕ) : ℤ),((dst0+j*L : ℕ) : ℤ),
      ((dst1+j*L : ℕ) : ℤ),q0,q1,ν₂,?_,?_,?_,?_⟩
    · simp [update_frame_setLocal]
    · intro a ha i hi
      by_cases haj : a = j
      · subst a
        constructor
        · rw [hkeep1 _ (Or.inl (by omega)),hout0 i hi,hread0' i hi,Nat.cast_mul]
        · simpa only [Nat.cast_mul] using (hout1 i hi).trans (by rw [hread1'' i hi])
      · have hal : a < j := by omega
        have he : a*L+i < j*L := by
          have hh := row_end_le (L := L) hal
          omega
        constructor
        · exact (hkeep1 _ (Or.inl (by omega))).trans
            ((hkeep0 _ (Or.inl (by omega))).trans (hrows a hal i hi).1)
        · exact (hkeep1 _ (Or.inl (by omega))).trans
            ((hkeep0 _ (Or.inr (by omega))).trans (hrows a hal i hi).2)
    · intro a ha
      exact (hkeep1 _ (Or.inl (by omega))).trans
        ((hkeep0 _ (Or.inl (by omega))).trans (hkept a ha))
    · intro a ha
      exact (hkeep1 _ (Or.inr (by omega))).trans
        ((hkeep0 _ (Or.inr (by omega))).trans (hpows a ha))
  case done =>
    rintro _ _ ⟨s,a,b,r0,r1,ν,rfl,hrows,hkept,hpows⟩
    exact ⟨hrows,hkept,hpows⟩
  case bound =>
    rintro j _ hj _ ⟨s,a,b,r0,r1,ν,rfl,_,_,_⟩
    (((try have := Light.Std.space_le (by assumption)));
      ((try have := Light.Std.const_le (by assumption)));
      (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))


























end ThreeSum.LightBlockCoefficients

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {pMain pPowers pScale : Nat},
  @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMain)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightBlockCoefficients.body pPowers pScale)) →
    @Eq.{1} (Option.{0} Light.Stmt)
        (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
          (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
          (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pPowers)
        (@Option.some.{0} Light.Stmt Light.powTableBody) →
      @Eq.{1} (Option.{0} Light.Stmt)
          (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
            (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
            (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pScale)
          (@Option.some.{0} Light.Stmt ThreeSum.LightScaleArray.body) →
        ∀ {μ : Nat → Int} {J L p occ maps dst0 dst1 work U M d : Nat} (sel : Nat → Nat) (w0 w1 : Nat → Nat → Nat),
          @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
            @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) p →
              @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) occ J) dst0 →
                @LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)
                        M))
                    dst0 →
                  @LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst0
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J L))
                      dst1 →
                    @LE.le.{0} Nat instLENat
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst1
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J L))
                        work →
                      @LE.le.{0} Nat instLENat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          lim.space →
                        @LE.le.{0} Int Int.instLEInt
                            (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightBlockCoefficients.word J p U)) lim.word →
                          @LT.lt.{0} Nat instLTNat d lim.depth →
                            (∀ (j : Nat), @LT.lt.{0} Nat instLTNat j J → @LT.lt.{0} Nat instLTNat (sel j) M) →
                              (∀ (j : Nat),
                                  @LT.lt.{0} Nat instLTNat j J →
                                    @Eq.{1} Int
                                      (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) occ j))
                                      (@Nat.cast.{0} Int instNatCastInt (sel j))) →
                                (∀ (s : Nat),
                                    @LT.lt.{0} Nat instLTNat s M →
                                      ∀ (i : Nat),
                                        @LT.lt.{0} Nat instLTNat i L →
                                          @Eq.{1} Int
                                            (μ
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)
                                                    s))
                                                i))
                                            (@Nat.cast.{0} Int instNatCastInt (w0 s i))) →
                                  (∀ (s : Nat),
                                      @LT.lt.{0} Nat instLTNat s M →
                                        ∀ (i : Nat),
                                          @LT.lt.{0} Nat instLTNat i L →
                                            @Eq.{1} Int
                                              (μ
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      maps
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          L)
                                                        s))
                                                    L)
                                                  i))
                                              (@Nat.cast.{0} Int instNatCastInt (w1 s i))) →
                                    (∀ (s : Nat),
                                        @LT.lt.{0} Nat instLTNat s M →
                                          ∀ (i : Nat),
                                            @LT.lt.{0} Nat instLTNat i L → @LE.le.{0} Nat instLENat (w0 s i) U) →
                                      (∀ (s : Nat),
                                          @LT.lt.{0} Nat instLTNat s M →
                                            ∀ (i : Nat),
                                              @LT.lt.{0} Nat instLTNat i L → @LE.le.{0} Nat instLENat (w1 s i) U) →
                                        Light.Meets lim P pMain d
                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt J)
                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt p)
                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt occ)
                                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt maps)
                                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst0)
                                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst1)
                                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                                          (@List.nil.{0} Int)))))))))
                                          μ (ThreeSum.LightBlockCoefficients.time J L) fun (x : Int) (ν : Nat → Int) =>
                                          And (ThreeSum.LightBlockCoefficients.Rows ν dst0 dst1 L p sel w0 w1 J)
                                            (And (Light.Kept μ ν dst0)
                                              (ThreeSum.LightBlockCoefficients.Powers ν work J p)) := by
  exact @ThreeSum.LightBlockCoefficients.meets_sourceProof

#print axioms solution
