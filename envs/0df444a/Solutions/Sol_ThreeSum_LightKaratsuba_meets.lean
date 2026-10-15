-- Prove2me | solution 1 for ThreeSum.LightKaratsuba.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:30:27.742621+00:00
-- url     : https://prove2.me/submissions/c3dfb094-f21c-419f-af4b-0b2721fc0d5f

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
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean.Elab.Tactic.Omega
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
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
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
import Theorems.Thm_ThreeSum_LightKaratsuba_recurse_ends


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba

section


/-!
# Dense integer Karatsuba multiplication

This file implements a dense, low-coefficient-first list algorithm. Its
correctness theorem is an equality of integer polynomials. The instrumented
work model counts list traversal and scalar arithmetic primitives; it is a
separate obligation to compile this implementation to `Light` and prove the
benchmark's word-RAM step and word-size bounds.
-/

namespace ThreeSum.Karatsuba

open Polynomial





















































































theorem asPolynomial_head {as : List ℤ} (h : as.length ≤ 1) :
    asPolynomial as = C (as.headD 0) := by
  cases as with
  | nil => simp [asPolynomial]
  | cons a as =>
    have hz : as.length = 0 := by simpa using h
    have he : as = [] := List.length_eq_zero_iff.mp hz
    subst as
    simp [asPolynomial]



































































/-! ## Explicit traversal/arithmetic work model

The following charges reflect the operations in the executable list code:
two units per matched coefficient of `plus`; two per mapped coefficient of
`negate`; two per generated/concatenated zero of `shift`; and the two scans
used by `take` and `drop`. The fixed per-call charges include list tests.
They are a conventional unit-cost list/arithmetic model, **not** a theorem
about the benchmark machine or Lean's runtime system.

The recursive charge below uses the actual intermediate list sizes. The
uniform three-subcall recurrence is proved from those sizes; it is not an
assumption that the desired multiplication bound already holds.
-/




















































































end ThreeSum.Karatsuba

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

theorem Ends.ite {σ T c s₁ s₂} {Q : State → Prop} (T' : ℕ) (hs : c.Safe lim σ)
    (h₁ : c.Holds σ → Ends lim P d s₁ σ T' Q) (h₂ : ¬ c.Holds σ → Ends lim P d s₂ σ T' Q)
    (hT : c.cost + 1 + T' ≤ T) : Ends lim P d (.ite c s₁ s₂) σ T Q := by
  by_cases hv : c.Holds σ
  · obtain ⟨σ', k, he, hk, hq⟩ := h₁ hv
    exact ⟨σ', _, .iteTrue hs hv he, by omega, hq⟩
  · obtain ⟨σ', k, he, hk, hq⟩ := h₂ hv
    exact ⟨σ', _, .iteFalse hs hv he, by omega, hq⟩

























































































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











































end

end Light

end
end

section


/-!
# Karatsuba as a fixed program in the benchmark language

The procedure below is a finite `Light.Stmt`, independent of the input
capacity. Recursive products share an eight-capacity scratch area. The
linear-time `half` routine avoids an additional persistent power table.
-/

namespace ThreeSum.LightKaratsuba

open Light
open ThreeSum.Karatsuba
open Polynomial

























































































































section Join

variable {lim : Limits} {P : Program} {d pLinear pFill : ℕ}




































































































































end Join

section BaseCase

variable {lim : Limits} {P : Program} {d : ℕ}

theorem base_ends {μ : ℕ → ℤ} {a b out work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a + 1 ≤ lim.space) (hb : b + 1 ≤ lim.space)
    (hout : out + 2 ≤ lim.space) (hmul : |μ a * μ b| ≤ lim.word) :
    Ends lim P d baseBody ⟨frame [1, a, b, out, work], μ⟩ 12 fun σ' =>
      σ'.mem out = μ a * μ b ∧ σ'.mem (out + 1) = 0 ∧
        SameOutside μ σ'.mem out 2 := by
  unfold baseBody
  have hm := abs_le.mp hmul
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.storeToThen out (μ a * μ b) ?_ ?_ ?_);
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
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.storeToThen (out + 1) 0 ?_ ?_ ?_);
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
  refine ⟨?_, ?_, ?_⟩
  · simp
  · simp
  · intro j hj
    simp only [Function.update_of_ne (by omega : j ≠ out + 1),
      Function.update_of_ne (by omega : j ≠ out)]

theorem base_product {μ μ' : ℕ → ℤ} {a b out : ℕ} {as bs : List ℤ}
    (ha : Seg μ a as) (hb : Seg μ b bs)
    (hAlen : as.length = 1) (hBlen : bs.length = 1)
    (hzero : μ' out = μ a * μ b) (hone : μ' (out + 1) = 0) :
    ProductAt μ' out 1 as bs := by
  have hA := asPolynomial_head hAlen.le
  have hB := asPolynomial_head hBlen.le
  have hhead (xs : List ℤ) : xs.getD 0 0 = xs.headD 0 := by cases xs <;> rfl
  have hreadA : μ a = as.headD 0 := by
    simpa only [Nat.add_zero, hhead] using ha.getD (by omega : 0 < as.length) 0
  have hreadB : μ b = bs.headD 0 := by
    simpa only [Nat.add_zero, hhead] using hb.getD (by omega : 0 < bs.length) 0
  intro j hj
  rw [hA, hB, ← map_mul]
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hj' with rfl | rfl
  · simpa only [Nat.add_zero, Polynomial.coeff_C_zero, hreadA, hreadB] using hzero
  · simpa only [Polynomial.coeff_C, if_neg (by decide : (1 : ℕ) ≠ 0)] using hone

end BaseCase


















































































theorem ten_temp_le_word (n U : ℕ) (hn : 0 < n) :
    10 * (4 * n * U ^ 2) ≤ wordBound n U := by
  have hn3 : n ≤ n ^ 3 := by nlinarith [Nat.one_le_pow 2 n hn]
  have hu : U ^ 2 ≤ (U + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hm := Nat.mul_le_mul hn3 hu
  unfold wordBound
  nlinarith
























section RecursiveExecution

variable {lim : Limits} {P : Program} {pSelf pHalf pLinear pFill : ℕ}











































































































































end RecursiveExecution

section CompleteProcedure

variable {lim : Limits} {P : Program} {pSelf pHalf pLinear pFill : ℕ}

/-- Correctness, preservation, word safety, call depth, and actual Light
step count for the fixed recursive multiplication procedure. -/
theorem meets_sourceProof (C : Procs P pSelf pHalf pLinear pFill)
    (hw : (lim.space : ℤ) ≤ lim.word)
    {k a b out work U : ℕ} {as bs : List ℤ} {μ : ℕ → ℤ}
    (hAlen : as.length = 2 ^ k) (hBlen : bs.length = 2 ^ k)
    (hAseg : Seg μ a as) (hBseg : Seg μ b bs)
    (hA : CoeffBound as (U : ℤ)) (hB : CoeffBound bs (U : ℤ))
    (haf : a + 2 ^ k ≤ work) (hbf : b + 2 ^ k ≤ work)
    (hof : out + 2 * 2 ^ k ≤ work) (hspace : work + 8 * 2 ^ k ≤ lim.space)
    (hword : (wordBound (2 ^ k) U : ℤ) ≤ lim.word) :
    ∀ d, d + k + 1 ≤ lim.depth →
      Meets lim P pSelf d [2 ^ k, a, b, out, work] μ (time k)
        (fun _ μ' => Result μ out (2 ^ k) work as bs μ') := by
  induction k generalizing a b out work U as bs μ with
  | zero =>
    simp only [pow_zero] at hAlen hBlen haf hbf hof hspace hword ⊢
    intro d hd
    have hvA : |μ a| ≤ (U : ℤ) := by
      have hr := hAseg.getD (by omega : 0 < as.length) 0
      simpa only [← hr, Nat.add_zero] using hA 0
    have hvB : |μ b| ≤ (U : ℤ) := by
      have hr := hBseg.getD (by omega : 0 < bs.length) 0
      simpa only [← hr, Nat.add_zero] using hB 0
    have hp : |μ a * μ b| ≤ (U : ℤ) ^ 2 := by
      rw [abs_mul, pow_two]
      exact mul_le_mul hvA hvB (abs_nonneg _) (Nat.cast_nonneg U)
    have hpw : (U : ℤ) ^ 2 ≤ lim.word := by
      have hh : 10 * ((4 * 1 * U ^ 2 : ℕ) : ℤ) ≤ wordBound 1 U := by
        exact_mod_cast ten_temp_le_word 1 U (by decide)
      push_cast at hh
      nlinarith only [hh, hword, sq_nonneg (U : ℤ)]
    have hbases := base_ends (P := P) (d := d) (a := a) (b := b) (out := out) (work := work)
      hw (by omega) (by omega) (by omega) (hp.trans hpw)
    refine Meets.of_body C.self ?_
    unfold body
    refine Ends.iteLast (fun hc => False.elim (by simpa using hc)) (fun _ => ?_)
      (hT := by simp [time, Cond.cost, Expr.cost])
    refine hbases.mono (by norm_num [time, Cond.cost, Expr.cost]) ?_
    intro σ' hr
    exact ⟨base_product hAseg hBseg hAlen hBlen hr.1 hr.2.1,
      fun j hj => hr.2.2 j hj.2⟩
  | succ k ih =>
    intro d hd
    have hp : 0 < (2 : ℕ) ^ k := Nat.pow_pos (by decide)
    have hpZ : (0 : ℤ) < (2 : ℤ) ^ k := pow_pos (by norm_num) k
    have he : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, Nat.mul_comm]
    have heZ : (2 : ℤ) ^ (k + 1) = 2 * ((2 ^ k : ℕ) : ℤ) := by
      push_cast
      rw [pow_succ, mul_comm]
    rw [he] at hAlen hBlen haf hbf hof hspace hword ⊢
    rw [heZ]
    refine Meets.of_body C.self ?_
    unfold body
    refine Ends.iteLast (fun _ => ?_) (fun hc => ?_)
      (hT := by first
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
                      | ((ring_nf); (omega))))
    · exact recurse_ends C rfl hw hAlen hBlen hAseg hBseg hA hB
        haf hbf hof hspace hword (by omega)
        (fun a' b' out' work' U' as' bs' μ' hla hlb hsa hsb hba hbb
          hfa hfb hfo hsp hwo =>
          ih hla hlb hsa hsb hba hbb hfa hfb hfo hsp hwo (d + 1) (by omega))
    · have hfalse : ¬ (1 : ℤ) < 2 * (2 : ℤ) ^ k := by simpa using hc
      have hone : (1 : ℤ) ≤ (2 : ℤ) ^ k := hpZ
      omega



















end CompleteProcedure

end ThreeSum.LightKaratsuba

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {pSelf pHalf pLinear pFill : Nat},
  ThreeSum.LightKaratsuba.Procs P pSelf pHalf pLinear pFill →
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
      ∀ {k a b out work U : Nat} {as bs : List.{0} Int} {μ : Nat → Int},
        @Eq.{1} Nat (@List.length.{0} Int as)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k) →
          @Eq.{1} Nat (@List.length.{0} Int bs)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k) →
            Light.Seg μ a as →
              Light.Seg μ b bs →
                ThreeSum.Karatsuba.CoeffBound as (@Nat.cast.{0} Int instNatCastInt U) →
                  ThreeSum.Karatsuba.CoeffBound bs (@Nat.cast.{0} Int instNatCastInt U) →
                    @LE.le.{0} Nat instLENat
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))
                        work →
                      @LE.le.{0} Nat instLENat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b
                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))
                          work →
                        @LE.le.{0} Nat instLENat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) out
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)))
                            work →
                          @LE.le.{0} Nat instLENat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                    (@instHPow.{0, 0} Nat Nat
                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)))
                              lim.space →
                            @LE.le.{0} Int Int.instLEInt
                                (@Nat.cast.{0} Int instNatCastInt
                                  (ThreeSum.LightKaratsuba.wordBound
                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                      (@instHPow.{0, 0} Nat Nat
                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
                                    U))
                                lim.word →
                              ∀ (d : Nat),
                                @LE.le.{0} Nat instLENat
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d k)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    lim.depth →
                                  Light.Meets lim P pSelf d
                                    (@List.cons.{0} Int
                                      (@HPow.hPow.{0, 0, 0} Int Nat Int
                                        (@instHPow.{0, 0} Int Nat
                                          (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                                        (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) k)
                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt b)
                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt out)
                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                              (@List.nil.{0} Int))))))
                                    μ (ThreeSum.LightKaratsuba.time k) fun (x : Int) (μ' : Nat → Int) =>
                                    ThreeSum.LightKaratsuba.Result μ out
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
                                      work as bs μ' := by
  exact @ThreeSum.LightKaratsuba.meets_sourceProof

#print axioms solution
