-- Prove2me | solution 1 for ThreeSum.LightCoverGreedy.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:12:45.511909+00:00
-- url     : https://prove2.me/submissions/16a580a3-ea5b-41f0-b63f-6698bcc8eb5e

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
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_Light_Ends_for
import Theorems.Thm_Light_Ends_pass
import Theorems.Thm_Light_seg_append
import Theorems.Thm_Light_seg_cons
import Theorems.Thm_ThreeSum_BooleanGreedy_active_succ
import Theorems.Thm_ThreeSum_BooleanGreedy_choice_eq_least
import Theorems.Thm_ThreeSum_LightCoverScores_meets
import Theorems.Thm_ThreeSum_LightCoverUpdate_meets
import Theorems.Thm_ThreeSum_LightMinimum_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BooleanGreedy
end ThreeSum.BooleanGreedy
namespace ThreeSumApsp
end ThreeSumApsp

section


/-! # An executable finite greedy cover and its logarithmic length bound -/

namespace ThreeSum.Cover

open Finset
open scoped BigOperators

variable {Ω U : Type*} [Inhabited Ω] [DecidableEq U]






theorem selectMap_mem (maps : List Ω) (hne : maps ≠ [])
    (covers : Ω → U → Prop) [DecidableRel covers] (targets : Finset U) :
    selectMap maps covers targets ∈ maps := by
  unfold selectMap
  cases h : maps.argmax (fun ω => (targets.filter (covers ω)).card) with
  | none => exact False.elim (hne (List.argmax_eq_none.mp h))
  | some ω =>
    simp only [Option.getD_some]
    exact List.argmax_mem (f := fun ω => (targets.filter (covers ω)).card)
      (by simpa only [Option.mem_def] using h)








































































































































end ThreeSum.Cover

end

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

/-- A piece of the program about which `h` is known, followed by the rest of the program, which gets
the steps that are left. -/
theorem Ends.pieceThen {σ : State} {T T₁ : ℕ} {s₁ s₂ : Stmt} {R Q : State → Prop}
    (h : Ends lim P d s₁ σ T₁ R) (rest : ∀ σ', R σ' → Ends lim P d s₂ σ' (T - T₁) Q)
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
  Ends.next T₁ (h.mono le_rfl rest) hT





































































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












@[simp] theorem Seg.nil : Seg μ a [] := fun i h => absurd h (by simp)


















































/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]
















/-- Writing outside a segment. -/
theorem Seg.update_out (h : Seg μ a l) (hb : b < a ∨ a + l.length ≤ b) (x : ℤ) :
    Seg (Function.update μ b x) a l :=
  h.congr fun i hi => Function.update_of_ne (by omega) _ _

/-- Writing just after a segment makes it longer. -/
theorem Seg.snoc (h : Seg μ a l) (x : ℤ) : Seg (Function.update μ (a + l.length) x) a (l ++ [x]) :=
  seg_append.2 ⟨h.update_out (Or.inr le_rfl) x, by simp [seg_cons]⟩







/-- A larger region may change. -/
theorem SameOutside.mono {a' n' : ℕ} (h : SameOutside μ μ' a n) (ha : a' ≤ a)
    (hn : a + n ≤ a' + n') :
    SameOutside μ μ' a' n' := fun b hb => h b (by omega)

/-- Writing inside the region. -/
theorem SameOutside.update (h : SameOutside μ μ' a n) (hb : a ≤ b ∧ b < a + n) (x : ℤ) :
    SameOutside μ (Function.update μ' b x) a n := fun c hc => by
  rw [Function.update_of_ne (by omega)]; exact h c hc









/-- A segment that does not meet the region is kept. -/
theorem Seg.of_sameOutside (h : Seg μ b l) (hs : SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : Seg μ' b l :=
  h.congr fun i hi => hs _ (by omega)












































































end Light

end
end

section


/-!
# A pass over an array

`pass c len dst e` is the loop "for c < len: dst[c] := e".  The rule `Ends.pass` says what it does:
if round j computes f j, then the loop writes f 0, …, f (n - 1) to the n cells from dst, changes
nothing else, and takes n (cost of e + 12) + 6 steps.  A routine whose only loop writes cell dst + c
in round c, with the length and dst in local variables, is an instance: its proof only says what
round j reads.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}




variable {μ : ℕ → ℤ} {dst j : ℕ} {f : ℕ → ℤ}

/-- After the pass the n cells hold the list of the values f 0, …, f (n - 1). -/
theorem seg_wrote {n : ℕ} {l : List ℤ} (hl : l.length = n)
    (h : ∀ i (hi : i < l.length), l[i] = f i) : Seg (wrote μ dst f n) dst l := fun i hi => by
  rw [wrote_done (hl ▸ hi), h i hi]



































end Light

end
end

section


/-!
# Copying and filling a segment

copy(src, dst, n) copies n cells from src to dst (the two segments do not overlap), within
`copyTime n` steps.  fill(dst, n, x) writes x into n cells from dst, within `fillTime n` steps.
Both change no other cell (`copy_meets`, `fill_meets`).  Each of the two is one pass over the cells
from dst, so `Ends.pass` says what it does, and the proof only says what round i reads.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## copy -/

namespace Copy







end Copy






















/-! ## fill -/

namespace Fill







end Fill








/-- **fill(dst, n, x)** writes x into the n cells from dst and changes nothing else. -/
theorem fill_meets {p : ℕ} (hp : P[p]? = some fillBody) {μ : ℕ → ℤ} {dst n : ℕ} {x : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + n ≤ lim.space) :
    Meets lim P p d [(dst : ℤ), n, x] μ (fillTime n) fun _ μ' =>
      Seg μ' dst (List.replicate n x) ∧ SameOutside μ μ' dst n :=
  .of_body hp (Ends.pass (fun _ => x) (fun i hi => by (((try have := Light.Std.space_le (by assumption)));
                                                        ((try have := Light.Std.const_le (by assumption)));
                                                        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    ⟨seg_wrote List.length_replicate fun i hi => List.getElem_replicate .., by ((try refine Light.SameOn.cell ?_); (intro apspMacro_28751_0 apspMacro_28751_1);
                                                                                   (first
                                                                                     |
                                                                                       ((((repeat
                                                                                                 (((with_reducible
                                                                                                         rename Light.SameOn _ _ _ => apspMacro_28751_2));
                                                                                                   ((try
                                                                                                         have :=
                                                                                                           apspMacro_28751_2 apspMacro_28751_0 (by omega)));
                                                                                                   (revert apspMacro_28751_2)));
                                                                                             (intros);
                                                                                             (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                         (omega))
                                                                                     |
                                                                                       ((simp [] at apspMacro_28751_1);
                                                                                         (((repeat
                                                                                                 (((with_reducible
                                                                                                         rename Light.SameOn _ _ _ => apspMacro_28751_3));
                                                                                                   ((try
                                                                                                         have :=
                                                                                                           apspMacro_28751_3 apspMacro_28751_0 (by omega)));
                                                                                                   (revert apspMacro_28751_3)));
                                                                                             (intros);
                                                                                             (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                         (omega))
                                                                                     |
                                                                                       ((((repeat
                                                                                                 (((with_reducible
                                                                                                         rename Light.SameOn _ _ _ => apspMacro_28751_4));
                                                                                                   ((try
                                                                                                         have :=
                                                                                                           apspMacro_28751_4 apspMacro_28751_0 (by omega)));
                                                                                                   (revert apspMacro_28751_4)));
                                                                                             (intros);
                                                                                             (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                         (fail
                                                                                             "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                                       SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                                       its condition K x does not follow from the hypotheses."))))⟩
    hw hdst rfl rfl (hT := by first
                              |
                                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fillTime]);
                                  (first
                                    | omega
                                    | ((ring_nf); (omega))))
                              | omega
                              |
                                (simp [fillTime] <;>
                                    first
                                    | omega
                                    | ((ring_nf); (omega)))))

end Light

end
end

section


/-! # Boolean-array semantics of the already specified finite greedy schedule -/

namespace ThreeSum.BooleanGreedy

open Finset
open scoped BigOperators





















theorem active_le (matrix : ℕ → ℕ → ℕ) (rows cols t j : ℕ) :
    active matrix rows cols t j ≤ 1 := by unfold active; split <;> omega

theorem active_zero {matrix : ℕ → ℕ → ℕ} {rows cols j : ℕ} (hj : j < cols) :
    active matrix rows cols 0 j = 1 := by simp [active,state,Cover.greedyState,hj]



























theorem choice_lt {matrix : ℕ → ℕ → ℕ} {rows cols : ℕ} (hrows : 0 < rows) (t : ℕ) :
    choice matrix rows cols t < rows := by
  apply List.mem_range.mp
  exact Cover.selectMap_mem _ (by simpa using hrows.ne') _ _


















































theorem choices_length (matrix : ℕ → ℕ → ℕ) (rows cols t : ℕ) :
    (choices matrix rows cols t).length = t := Cover.greedyChoices_length ..

theorem choices_succ (matrix : ℕ → ℕ → ℕ) (rows cols t : ℕ) :
    choices matrix rows cols (t+1) = choices matrix rows cols t ++ [choice matrix rows cols t] := rfl

end ThreeSum.BooleanGreedy

end

section


/-! # Actual first-maximum candidate selection from a Boolean cover matrix -/

namespace ThreeSum.LightCoverSelect

open Light








variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain pScores pDot pMinimum : ℕ}
    (hmain : P[pMain]? = some (body pScores pMinimum))
    (hscores : P[pScores]? = some (LightCoverScores.body pDot))
    (hdot : P[pDot]? = some LightBooleanDot.body)
    (hminimum : P[pMinimum]? = some LightMinimum.body)
    {μ : ℕ → ℤ} {src activePtr work rows cols : ℕ}
    (matrix : ℕ → ℕ → ℕ) (active : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hrows : 0 < rows)
    (hsrc : src+rows*cols ≤ work) (hactive : activePtr+cols ≤ work)
    (hspace : work+rows ≤ lim.space)
    (hread : ∀ i < rows, ∀ j < cols, μ (src+i*cols+j) = (matrix i j : ℤ))
    (hreadActive : ∀ j < cols, μ (activePtr+j) = (active j : ℤ))
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1)
    (hactiveValue : ∀ j < cols, active j ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim P pMain d [src,activePtr,work,rows,cols] μ (time rows cols)
      (fun r μ' =>
        r = (LightMinimum.least (fun i => -(LightCoverScores.score matrix active cols i : ℤ)) rows : ℤ) ∧
        SameOutside μ μ' work rows) := by
  apply Meets.of_body hmain
  unfold body time
  have hc := LightCoverScores.meets (d := d+1) (μ := μ)
    (src := src) (activePtr := activePtr) (dst := work) (rows := rows) (cols := cols)
    hscores hdot matrix active hw hd hsrc hactive hspace hread hreadActive hmatrix hactiveValue hword
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
      | refine Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hc ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightCoverScores.time, LightBooleanDot.time, LightMinimum.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightCoverScores.time, LightBooleanDot.time,
                LightMinimum.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, LightCoverScores.time,
                LightBooleanDot.time, LightMinimum.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro v μ₁ ⟨written, kept⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hm := LightMinimum.meets (d := d+1) (μ := μ₁) (src := work) (n := rows)
    hminimum (fun i => -(LightCoverScores.score matrix active cols i : ℤ))
    hw hrows hspace written
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
      | refine Light.Ends.callToThen (hm _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hm ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightCoverScores.time, LightBooleanDot.time, LightMinimum.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightCoverScores.time, LightBooleanDot.time,
                LightMinimum.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, LightCoverScores.time,
                LightBooleanDot.time, LightMinimum.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro r μ₂ ⟨hr, hmem⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  subst μ₂
  exact ⟨hr,kept⟩










theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {src activePtr work rows cols : ℕ}
    (matrix : ℕ → ℕ → ℕ) (active : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hrows : 0 < rows)
    (hsrc : src+rows*cols ≤ work) (hactive : activePtr+cols ≤ work)
    (hspace : work+rows ≤ lim.space)
    (hread : ∀ i < rows, ∀ j < cols, μ (src+i*cols+j) = (matrix i j : ℤ))
    (hreadActive : ∀ j < cols, μ (activePtr+j) = (active j : ℤ))
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1)
    (hactiveValue : ∀ j < cols, active j ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim P pMain d [src,activePtr,work,rows,cols] μ (time rows cols)
      (fun r μ' =>
        r = (LightMinimum.least (fun i => -(LightCoverScores.score matrix active cols i : ℤ)) rows : ℤ) ∧
        SameOutside μ μ' work rows) :=
  LightCoverSelect.meets S.main S.scores S.dot S.minimum matrix active hw hd hrows
    hsrc hactive hspace hread hreadActive hmatrix hactiveValue hword























end ThreeSum.LightCoverSelect

end

section


/-!
# An actual exhaustive finite greedy-cover program

The candidate matrix is read-only. The routine initializes active targets,
computes every candidate score, chooses the first maximum, stores the
chosen index, and removes its covered targets. Its output is exactly the
pre-existing `Cover.greedyChoices` list, including repeated occurrences.
-/

namespace ThreeSum.LightCoverGreedy

open Light BooleanGreedy

set_option maxHeartbeats 1200000
set_option maxRecDepth 5000








































variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets_sourceProof {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {src activePtr rows cols rounds : ℕ}
    (matrix : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hrows : 0 < rows)
    (hsrc : src+rows*cols ≤ activePtr)
    (hspace : activePtr+total rows cols rounds ≤ lim.space)
    (hread : ∀ i < rows, ∀ j < cols, μ (src+i*cols+j) = (matrix i j : ℤ))
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim P pMain d [src,activePtr,rows,cols,rounds] μ (time rows cols rounds)
      (fun r μ' => r = (out activePtr rows cols : ℤ) ∧
        Seg μ' (out activePtr rows cols) ((choices matrix rows cols rounds).map (fun x : ℕ => (x : ℤ))) ∧
        (∀ j < cols, μ' (activePtr+j) = (active matrix rows cols rounds j : ℤ)) ∧
        SameOutside μ μ' activePtr (total rows cols rounds)) := by
  have hspace' : activePtr+cols+rows+rounds ≤ lim.space := by simpa [total,Nat.add_assoc] using hspace
  have hworkSpace : activePtr+cols+rows ≤ lim.space := by omega
  have hactiveSpace : activePtr+cols ≤ lim.space := by omega
  have houtSpace : out activePtr rows cols+rounds ≤ lim.space := by simpa [out] using hspace'
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
    (refine Light.Ends.setToThen (activePtr + cols : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, out,
                roundTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [out, roundTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, out, roundTime] <;>
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
    (refine Light.Ends.setToThen (out activePtr rows cols : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, out,
                roundTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [out, roundTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, out, roundTime] <;>
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
            ((fill_meets (d := d + 1) (μ := μ) (dst := activePtr) (n := cols)
                (x := 1) S.fill hw hactiveSpace)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (fill_meets (d := d + 1) (μ := μ) (dst := activePtr) (n := cols) (x :=
              1) S.fill hw hactiveSpace)
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, out,
                roundTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [out, roundTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, out, roundTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro vf μ₁ ⟨hfill, hkept⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  refine Ends.pieceThen (Ends.for (T := rounds*(roundTime rows cols+8)+6)
    (Q := fun σ => Inv μ matrix src activePtr rows cols rounds rounds σ)
    (Inv μ matrix src activePtr rows cols rounds) rounds (roundTime rows cols)
    ?_ ?_ ?_ ?_ (hT := by first
                          |
                            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, roundTime]);
                              (first
                                | omega
                                | ((ring_nf); (omega))))
                          | omega
                          |
                            (simp [roundTime] <;>
                                first
                                | omega
                                | ((ring_nf); (omega))))) ?_
  · refine ⟨0,vf,μ₁,?_,?_,?_,?_⟩
    · simp [Inv,update_frame_setLocal,out]
    · intro j hj
      rw [active_zero hj]
      exact (hfill j (by simpa using hj)).trans (List.getElem_replicate ..)
    · simp [choices,Cover.greedyChoices]
    · exact hkept.mono le_rfl (by unfold total; omega)
  · rintro i _ hi _ ⟨r,v,μ',rfl,hactive,written,kept⟩
    have hmread : ∀ a < rows, ∀ j < cols, μ' (src+a*cols+j) = (matrix a j : ℤ) := by
      intro a ha j hj
      have hm : (a+1)*cols ≤ rows*cols := Nat.mul_le_mul_right cols (by omega)
      have haddr : src+a*cols+j < activePtr := by nlinarith
      rw [kept _ (Or.inl haddr)]
      exact hread a ha j hj
    have hchoice := choice_lt (matrix := matrix) (cols := cols) hrows i
    have hcWord : (choice matrix rows cols i : ℤ) ≤ lim.word := by
      have hh : choice matrix rows cols i ≤ lim.space := by omega
      exact (Int.ofNat_le.mpr hh).trans hw
    unfold roundBody
    have hs := S.select.meets (d := d+1) (μ := μ')
      (src := src) (activePtr := activePtr) (work := activePtr+cols) (rows := rows) (cols := cols)
      matrix (active matrix rows cols i) hw (by omega) hrows (by omega) le_rfl
      hworkSpace hmread hactive hmatrix (fun j _ => active_le matrix rows cols i j) hword
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
        | refine Light.Ends.callToThen (hs _ (by omega)) ?_ ?_ ?_ ?_
        | refine Light.Ends.callToThen hs ?_ ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  roundTime, LightCoverSelect.time, LightCoverScores.time,
                  LightBooleanDot.time, LightCoverUpdate.time, LightMinimum.time,
                  out]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [roundTime, LightCoverSelect.time, LightCoverScores.time,
                  LightBooleanDot.time, LightCoverUpdate.time, LightMinimum.time,
                  out] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 => omega);
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, roundTime,
                  LightCoverSelect.time, LightCoverScores.time,
                  LightBooleanDot.time, LightCoverUpdate.time, LightMinimum.time,
                  out] <;>
                omega)));
      (on_goal -1 =>
          ((rintro selected μ₂ ⟨hselected, hkeep₂⟩);
            (try with_unfolding_none refine Light.Ends.skip ?_)))
    have hselected' : selected = (choice matrix rows cols i : ℤ) := by
      rw [hselected,choice_eq_least hrows hmatrix i]
    have hactive₂ : ∀ j < cols, μ₂ (activePtr+j) = (active matrix rows cols i j : ℤ) := by
      intro j hj
      rw [hkeep₂ _ (Or.inl (by omega))]
      exact hactive j hj
    have hwritten₂ : Seg μ₂ (out activePtr rows cols)
        ((choices matrix rows cols i).map (fun x : ℕ => (x : ℤ))) :=
      written.of_sameOutside hkeep₂ (Or.inr (by unfold out; omega))
    have hkeep₂full : SameOutside μ μ₂ activePtr (total rows cols rounds) := by
      intro a ha
      rw [hkeep₂ _ (by unfold total at ha; omega)]
      exact kept a ha
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
          Light.Ends.storeToThen (out activePtr rows cols + i)
            (choice matrix rows cols i : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  hselected', roundTime, LightCoverSelect.time,
                  LightCoverScores.time, LightBooleanDot.time,
                  LightCoverUpdate.time, LightMinimum.time, out]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hselected', roundTime, LightCoverSelect.time,
                  LightCoverScores.time, LightBooleanDot.time,
                  LightCoverUpdate.time, LightMinimum.time, out] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hselected', roundTime,
                  LightCoverSelect.time, LightCoverScores.time,
                  LightBooleanDot.time, LightCoverUpdate.time, LightMinimum.time,
                  out] <;>
                omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    let μ₃ := Function.update μ₂ (out activePtr rows cols+i) (choice matrix rows cols i : ℤ)
    have hchoices₃ : Seg μ₃ (out activePtr rows cols)
        ((choices matrix rows cols (i+1)).map (fun x : ℕ => (x : ℤ))) := by
      have hh := hwritten₂.snoc (choice matrix rows cols i : ℤ)
      simpa [choices_succ,List.map_append,List.map_singleton,choices_length,μ₃] using hh
    have hactive₃ : ∀ j < cols, μ₃ (activePtr+j) = (active matrix rows cols i j : ℤ) := by
      intro j hj
      rw [show μ₃ (activePtr+j) = μ₂ (activePtr+j) by
        unfold μ₃; rw [Function.update_of_ne (by unfold out; omega)]]
      exact hactive₂ j hj
    have hkeep₃ : SameOutside μ μ₃ activePtr (total rows cols rounds) :=
      hkeep₂full.update ⟨by unfold out; omega,by unfold out total; omega⟩ _
    have hmul : (choice matrix rows cols i+1)*cols ≤ rows*cols := Nat.mul_le_mul_right cols (by omega)
    have hrow : src+choice matrix rows cols i*cols+cols ≤ activePtr := by nlinarith
    have hrowSpace : src+choice matrix rows cols i*cols+cols ≤ lim.space := by omega
    have hrowRead : ∀ j < cols,
        μ₃ (src+choice matrix rows cols i*cols+j) = (matrix (choice matrix rows cols i) j : ℤ) := by
      intro j hj
      rw [hkeep₃ _ (Or.inl (by omega))]
      exact hread _ hchoice j hj
    have hmulWord : ((choice matrix rows cols i*cols : ℕ) : ℤ) ≤ lim.word := by
      have hh : choice matrix rows cols i*cols ≤ lim.space := by omega
      exact (Int.ofNat_le.mpr hh).trans hw
    have haddr : ((src : ℤ)+(choice matrix rows cols i : ℤ)*cols).toNat =
        src+choice matrix rows cols i*cols := by
      rw [← Nat.cast_mul,← Nat.cast_add,Int.toNat_natCast]
    have hu := LightCoverUpdate.meets (d := d+1) (μ := μ₃)
      (row := src+choice matrix rows cols i*cols) (activePtr := activePtr) (n := cols)
      S.update (matrix (choice matrix rows cols i)) (active matrix rows cols i) hw hrowSpace
      hactiveSpace (Or.inl hrow) hrowRead hactive₃ (hmatrix _ hchoice)
      (fun j _ => active_le matrix rows cols i j) hword
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
        | refine Light.Ends.callToThen (hu _ (by omega)) ?_ ?_ ?_ ?_
        | refine Light.Ends.callToThen hu ?_ ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  hselected', haddr, μ₃, roundTime, LightCoverSelect.time,
                  LightCoverScores.time, LightBooleanDot.time,
                  LightCoverUpdate.time, LightMinimum.time, out]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hselected', haddr, μ₃, roundTime, LightCoverSelect.time,
                  LightCoverScores.time, LightBooleanDot.time,
                  LightCoverUpdate.time, LightMinimum.time, out] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 => omega);
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hselected', haddr, μ₃,
                  roundTime, LightCoverSelect.time, LightCoverScores.time,
                  LightBooleanDot.time, LightCoverUpdate.time, LightMinimum.time,
                  out] <;>
                omega)));
      (on_goal -1 =>
          ((rintro vnew μ₄ ⟨hnewActive, hkeep₄⟩);
            (try with_unfolding_none refine Light.Ends.skip ?_)))
    refine ⟨by simp,selected,vnew,μ₄,by simp [update_frame_setLocal],?_,?_,?_⟩
    · intro j hj
      rw [hnewActive j hj,active_succ hrows hmatrix i j hj]
    · exact hchoices₃.of_sameOutside hkeep₄ (Or.inr (by unfold out; omega))
    · intro a ha
      rw [hkeep₄ _ (by unfold total at ha; omega)]
      exact hkeep₃ a ha
  · intro σ hcounter hshape
    exact hshape
  · rintro i _ _ _ ⟨r,v,μ',rfl,_,_,_⟩
    simp
  · rintro σ ⟨r,v,μ',rfl,hactive,written,kept⟩
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (out activePtr rows cols : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, out,
                  roundTime]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [out, roundTime] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, out, roundTime] <;>
                omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    exact ⟨rfl,written,hactive,kept⟩

























end ThreeSum.LightCoverGreedy

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (S : ThreeSum.LightCoverGreedy.Procs P pMain) {μ : Nat → Int}
  {src activePtr rows cols rounds : Nat} (matrix : Nat → Nat → Nat),
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    @LT.lt.{0} Nat instLTNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        lim.depth →
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) rows →
        @LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) rows cols))
            activePtr →
          @LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) activePtr
                (ThreeSum.LightCoverGreedy.total rows cols rounds))
              lim.space →
            (∀ (i : Nat),
                @LT.lt.{0} Nat instLTNat i rows →
                  ∀ (j : Nat),
                    @LT.lt.{0} Nat instLTNat j cols →
                      @Eq.{1} Int
                        (μ
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i cols))
                            j))
                        (@Nat.cast.{0} Int instNatCastInt (matrix i j))) →
              (∀ (i : Nat),
                  @LT.lt.{0} Nat instLTNat i rows →
                    ∀ (j : Nat),
                      @LT.lt.{0} Nat instLTNat j cols →
                        @LE.le.{0} Nat instLENat (matrix i j)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))) lim.word →
                  Light.Meets lim P pMain d
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt activePtr)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rows)
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cols)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rounds) (@List.nil.{0} Int))))))
                    μ (ThreeSum.LightCoverGreedy.time rows cols rounds) fun (r : Int) (μ' : Nat → Int) =>
                    And
                      (@Eq.{1} Int r
                        (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightCoverGreedy.out activePtr rows cols)))
                      (And
                        (Light.Seg μ' (ThreeSum.LightCoverGreedy.out activePtr rows cols)
                          (@List.map.{0, 0} Nat Int (fun (x : Nat) => @Nat.cast.{0} Int instNatCastInt x)
                            (ThreeSum.BooleanGreedy.choices matrix rows cols rounds)))
                        (And
                          (∀ (j : Nat),
                            @LT.lt.{0} Nat instLTNat j cols →
                              @Eq.{1} Int
                                (μ' (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) activePtr j))
                                (@Nat.cast.{0} Int instNatCastInt
                                  (ThreeSum.BooleanGreedy.active matrix rows cols rounds j)))
                          (Light.SameOutside μ μ' activePtr (ThreeSum.LightCoverGreedy.total rows cols rounds)))) := by
  exact @ThreeSum.LightCoverGreedy.Procs.meets_sourceProof

#print axioms solution
