-- Prove2me | solution 1 for ThreeSum.LightWeightedScore.meets_of_count_backend
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:02:20.679099+00:00
-- url     : https://prove2.me/submissions/6693a4a8-5f77-477d-b31c-6f21ad6d3e5f

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
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Equiv.Basic
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
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Theorems.Thm_Light_Ends_for
import Theorems.Thm_Light_emod_meets
import Theorems.Thm_ThreeSum_WeightedScore_score_eq_remaining


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.Arithmetic
end ThreeSum.Arithmetic
namespace ThreeSum.LightResidueHistogram
end ThreeSum.LightResidueHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.ModuloCounts
end ThreeSum.ModuloCounts
namespace ThreeSum.WeightedModuli
end ThreeSum.WeightedModuli
namespace ThreeSum.WeightedScore
end ThreeSum.WeightedScore

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
























theorem emodTime_le {x : ℤ} {p U : ℕ} (hx : |x| ≤ (U : ℤ)) :
    emodTime x.natAbs p ≤ residueBudget U := by
  have hU : x.natAbs ≤ U := by simpa only [← Int.natCast_natAbs, Nat.cast_le] using hx
  have h := emodRounds_le (M := p) hU
  unfold emodTime residueBudget
  omega





















































































end ThreeSum.LightResidues

end

section


/-!
# Weighted counting with possibly shared prime factors

For prime `p`, simultaneous divisibility by `q` and `p` is tested at `q`
when `p ∣ q`, and at `q*p` otherwise. This executable branch permits one
finite prime pool to supply both contraction and auxiliary tests.
-/

namespace ThreeSum.WeightedModuli

open Finset Arithmetic
open scoped BigOperators



theorem joint_le_mul (q p : ℕ) (hp : 1 ≤ p) : joint q p ≤ q * p := by
  unfold joint
  split
  · exact Nat.le_mul_of_pos_right q hp
  · exact le_rfl

theorem joint_positive {q p : ℕ} (hq : 0 < q) (hp : Nat.Prime p) :
    0 < joint q p := by
  unfold joint
  split
  · exact hq
  · exact Nat.mul_pos hq hp.pos































































end ThreeSum.WeightedModuli

end

section


/-!
# Modular triple counts from the original integer arrays

This interface identifies the executable histogram/correlation lookup with
the exact `Arithmetic.modCount` used in the weighted false-triple argument.
The three indices retain their multiplicities even when input values repeat.
-/

namespace ThreeSum.ModuloCounts

open Finset LightResidueHistogram
open scoped BigOperators



































theorem count_le (p nA nB nC : ℕ) (a b c : ℕ → ℤ) :
    count p nA nB nC a b c ≤ nA*nB*nC := by
  have h : count p nA nB nC a b c ≤ (triples nA nB nC).card := by
    unfold count Arithmetic.modCount
    calc
      _ ≤ ∑ _t ∈ triples nA nB nC, (1 : ℕ) := by
        apply sum_le_sum
        intro t ht
        unfold Arithmetic.dividesIndicator
        split <;> omega
      _ = _ := by simp
  simpa only [triples, card_product, card_range, Nat.mul_assoc] using h




















end ThreeSum.ModuloCounts

end

section


/-!
# Array-order identities for the weighted modular score

The auxiliary primes are read in a fixed array order.  Every partial
correction is at most the initial `s * N_q`, so the corresponding machine
subtractions stay nonnegative.  Shared factors with `q` use `joint`.
-/

namespace ThreeSum.WeightedScore

open Finset Arithmetic ModuloCounts WeightedModuli
open scoped BigOperators
















theorem count_mono_dvd {q r : ℕ} (h : q ∣ r) (nA nB nC : ℕ)
    (a b c : ℕ → ℤ) : count r nA nB nC a b c ≤ count q nA nB nC a b c := by
  unfold count modCount
  apply sum_le_sum
  intro t ht
  have hdiv : (q : ℤ) ∣ (r : ℤ) := Int.natCast_dvd_natCast.mpr h
  unfold dividesIndicator
  by_cases hr : (r : ℤ) ∣ difference a b c t
  · simp [hr, hdiv.trans hr]
  · simp [hr]

theorem base_dvd_joint (q p : ℕ) : q ∣ joint q p := by
  unfold joint
  split
  · exact dvd_refl q
  · exact dvd_mul_right q p

theorem joint_count_le (q p nA nB nC : ℕ) (a b c : ℕ → ℤ) :
    count (joint q p) nA nB nC a b c ≤ count q nA nB nC a b c :=
  count_mono_dvd (base_dvd_joint q p) nA nB nC a b c

@[simp] theorem corrections_zero (primes : ℕ → ℕ) (q nA nB nC : ℕ)
    (a b c : ℕ → ℤ) : corrections primes q nA nB nC a b c 0 = 0 := by
  simp [corrections]

theorem corrections_succ (primes : ℕ → ℕ) (q nA nB nC : ℕ)
    (a b c : ℕ → ℤ) (i : ℕ) :
    corrections primes q nA nB nC a b c (i+1) =
      corrections primes q nA nB nC a b c i +
        count (joint q (primes i)) nA nB nC a b c := by
  exact sum_range_succ _ _

theorem corrections_le (primes : ℕ → ℕ) (q nA nB nC : ℕ)
    (a b c : ℕ → ℤ) (i : ℕ) :
    corrections primes q nA nB nC a b c i ≤ i * count q nA nB nC a b c := by
  unfold corrections
  calc
    _ ≤ ∑ _j ∈ range i, count q nA nB nC a b c :=
      sum_le_sum fun j _ => joint_count_le q (primes j) nA nB nC a b c
    _ = _ := by simp

@[simp] theorem remaining_zero (primes : ℕ → ℕ) (s q nA nB nC : ℕ)
    (a b c : ℕ → ℤ) :
    remaining primes s q nA nB nC a b c 0 = s * count q nA nB nC a b c := by
  simp [remaining]

theorem remaining_le (primes : ℕ → ℕ) (s q nA nB nC : ℕ)
    (a b c : ℕ → ℤ) (i : ℕ) :
    remaining primes s q nA nB nC a b c i ≤ s * (nA*nB*nC) :=
  (Nat.sub_le _ _).trans (Nat.mul_le_mul_left s (count_le q nA nB nC a b c))

theorem next_count_le_remaining (primes : ℕ → ℕ) {s q nA nB nC i : ℕ}
    (a b c : ℕ → ℤ) (hi : i < s) :
    count (joint q (primes i)) nA nB nC a b c ≤
      remaining primes s q nA nB nC a b c i := by
  have h := (corrections_le primes q nA nB nC a b c (i+1)).trans
    (Nat.mul_le_mul_right (count q nA nB nC a b c) (by omega : i+1 ≤ s))
  rw [corrections_succ] at h
  unfold remaining
  omega

theorem remaining_succ (primes : ℕ → ℕ) (s q nA nB nC : ℕ)
    (a b c : ℕ → ℤ) (i : ℕ) :
    remaining primes s q nA nB nC a b c (i+1) =
      remaining primes s q nA nB nC a b c i -
        count (joint q (primes i)) nA nB nC a b c := by
  unfold remaining
  rw [corrections_succ, Nat.sub_add_eq]

theorem remaining_succ_cast (primes : ℕ → ℕ) {s q nA nB nC i : ℕ}
    (a b c : ℕ → ℤ) (hi : i < s) :
    (remaining primes s q nA nB nC a b c (i+1) : ℤ) =
      (remaining primes s q nA nB nC a b c i : ℤ) -
        (count (joint q (primes i)) nA nB nC a b c : ℤ) := by
  rw [remaining_succ, Nat.cast_sub (next_count_le_remaining primes a b c hi)]





































end ThreeSum.WeightedScore

end

section


/-!
# Executing the weighted modular score

The joint-modulus helper uses the verified division-free remainder routine.
The score loop computes a base count, then visits the auxiliary-prime array
once.  All calls reuse the same scratch region and preserve the original
arrays.  Its intermediate scores are proved nonnegative.

The generic loop theorem exposes the modular-counting execution contract.
The concrete wrapper instantiates that contract with the checked fixed
modular-counting program; no counting operation is added to the machine.
-/

namespace ThreeSum.LightWeightedScore

open Light WeightedModuli WeightedScore LightResidues

variable {lim : Limits} {P : Program} {d : ℕ}

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000








theorem joint_meets {pJoint pEmod : ℕ}
    (hjoint : P[pJoint]? = some (jointBody pEmod))
    (hem : P[pEmod]? = some emodBody)
    {μ : ℕ → ℤ} {q p maxMod free : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hq : 0 < q) (hp : 0 < p) (hmax : q*p ≤ maxMod)
    (hspace : free + (Nat.log 2 (maxMod+1)+2) ≤ lim.space)
    (hword : (8*maxMod+16 : ℕ) ≤ lim.word) :
    Meets lim P pJoint d [q,p,free] μ (jointTime maxMod)
      fun r μ' => r = (joint q p : ℤ) ∧ Kept μ μ' free := by
  have hqmax : q ≤ maxMod := (Nat.le_mul_of_pos_right q hp).trans hmax
  have hpmax : p ≤ maxMod := (Nat.le_mul_of_pos_left p hq).trans hmax
  have hpre : Emod.Pre lim p maxMod free := ⟨hp, hw, by
    have hpZ : (p : ℤ) ≤ maxMod := by exact_mod_cast hpmax
    have hwZ : (8*(maxMod : ℤ)+16) ≤ lim.word := by exact_mod_cast hword
    omega, hspace⟩
  have hx : |(q : ℤ)| ≤ (maxMod : ℤ) := by simpa using (Int.ofNat_le.mpr hqmax)
  have ht := emodTime_le (p := p) hx
  simp only [Int.natAbs_natCast] at ht
  unfold emodTime residueBudget at ht
  have hlog : Nat.log 2 (1+maxMod) = Nat.log 2 (maxMod+1) := by rw [Nat.add_comm]
  have hmulZ : (q : ℤ)*(p : ℤ) ≤ lim.word := by
    have hh : ((q*p : ℕ) : ℤ) ≤ (maxMod : ℤ) := by exact_mod_cast hmax
    have hwZ : (8*(maxMod : ℤ)+16) ≤ lim.word := by exact_mod_cast hword
    push_cast at hh
    omega
  apply Meets.of_body hjoint
  unfold jointBody jointTime
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
            ((emod_meets (x := (q : ℤ)) hem hpre hx) _ (by omega)) ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen (emod_meets (x := (q : ℤ)) hem hpre hx) ?_ ?_ ?_
            ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                residueBudget]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [residueBudget] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, residueBudget] <;> omega)));
    (on_goal -1 =>
        ((rintro result μ₁ ⟨hresult, hkeep⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  subst result
  refine Ends.iteLast (fun hz => ?_) (fun hnz => ?_) (by (((try have := Light.Std.space_le (by assumption)));
                                                           ((try have := Light.Std.const_le (by assumption)));
                                                           (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT := by first
              |
                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                      residueBudget]);
                  (first
                    | omega
                    | ((ring_nf); (omega))))
              | omega
              |
                (simp [residueBudget] <;>
                    first
                    | omega
                    | ((ring_nf); (omega))))
  · have hdiv : p ∣ q := by
      have hh : (q : ℤ) % (p : ℤ) = 0 := by simpa using hz
      exact Int.natCast_dvd_natCast.mp (Int.dvd_of_emod_eq_zero hh)
    apply Ends.skip
    exact ⟨by simp [joint,hdiv],hkeep⟩
  · have hnot : ¬ p ∣ q := by
      intro hh
      apply hnz
      have he : (q : ℤ) % (p : ℤ) = 0 :=
        Int.emod_eq_zero_of_dvd (Int.natCast_dvd_natCast.mpr hh)
      simpa using he
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (q * p : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  jointTime, residueBudget]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [jointTime, residueBudget] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, jointTime,
                  residueBudget] <;>
                omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    exact ⟨by simp [joint,hnot],hkeep⟩

























theorem meets_of_count_backend_sourceProof {pMain pCount pJoint pEmod : ℕ}
    (hmain : P[pMain]? = some (body pCount pJoint))
    (hjoint : P[pJoint]? = some (jointBody pEmod))
    (hem : P[pEmod]? = some emodBody)
    {μ : ℕ → ℤ} {a b c nA nB nC q N aux s free maxMod countTime : ℕ}
    (primes : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hq : 0 < q) (hqmax : q ≤ maxMod)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (haux : aux+s ≤ free) (hN : N ≤ lim.space)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : free+(Nat.log 2 (maxMod+1)+2) ≤ lim.space)
    (hword : ((s+1)*N^3+8*maxMod+16 : ℕ) ≤ lim.word)
    (hread : ∀ i < s, μ (aux+i) = (primes i : ℤ))
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j)
    (hproduct : ∀ i < s, q*primes i ≤ maxMod)
    (hcount : ∀ (ν : ℕ → ℤ) (p : ℕ), Kept μ ν free → 0 < p → p ≤ maxMod →
      Meets lim P pCount (d+1) [a,b,c,nA,nB,nC,p,N,free] ν countTime
        (fun r ν' => r = (ModuloCounts.count p nA nB nC
          (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) : ℤ) ∧
          Kept ν ν' free)) :
    Meets lim P pMain d [a,b,c,nA,nB,nC,q,N,aux,s,free] μ (time countTime s maxMod)
      fun r μ' => r = (score primes s q nA nB nC
        (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) : ℤ) ∧
          Kept μ μ' free := by
  let A := fun j => μ (a+j)
  let B := fun j => μ (b+j)
  let C := fun j => μ (c+j)
  let base := ModuloCounts.count q nA nB nC A B C
  have hprodN : nA*nB*nC ≤ N^3 := by
    calc
      _ ≤ N*N*N := Nat.mul_le_mul (Nat.mul_le_mul hnA hnB) hnC
      _ = _ := by ring
  have hbase : base ≤ N^3 := (ModuloCounts.count_le q nA nB nC A B C).trans hprodN
  have hbound (i : ℕ) : remaining primes s q nA nB nC A B C i ≤ s*N^3 :=
    (remaining_le primes s q nA nB nC A B C i).trans (Nat.mul_le_mul_left s hprodN)
  have hbaseZ : (base : ℤ) ≤ lim.word := by
    have hm : N^3 ≤ (s+1)*N^3+8*maxMod+16 := by nlinarith
    exact (Int.ofNat_le.mpr (hbase.trans hm)).trans hword
  have hscoreZ (i : ℕ) : (remaining primes s q nA nB nC A B C i : ℤ) ≤ lim.word := by
    have hm : s*N^3 ≤ (s+1)*N^3+8*maxMod+16 := by nlinarith
    exact (Int.ofNat_le.mpr ((hbound i).trans hm)).trans hword
  have hinitZ : ((s*base : ℕ) : ℤ) ≤ lim.word := by
    simpa only [remaining_zero] using hscoreZ 0
  have hinitNonneg : (0 : ℤ) ≤ (s : ℤ) * (base : ℤ) := by positivity
  dsimp [base,A,B,C] at hinitZ hinitNonneg
  have hjword : (8*maxMod+16 : ℕ) ≤ lim.word := by
    have hh : 8*maxMod+16 ≤ (s+1)*N^3+8*maxMod+16 := by omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hNword : (N : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hN).trans hw
  have hmodword : (maxMod : ℤ) ≤ lim.word := by
    have hwZ : (8*(maxMod : ℤ)+16) ≤ lim.word := by exact_mod_cast hjword
    omega
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
            ((hcount μ q (fun _ _ => rfl) hq hqmax) _ (by omega)) ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen (hcount μ q (fun _ _ => rfl) hq hqmax) ?_ ?_ ?_
            ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, A, B, C,
                base]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [A, B, C, base] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, A, B, C, base] <;> omega)));
    (on_goal -1 =>
        ((rintro res μ₀ ⟨hres, hkept₀⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hres' : res = (base : ℤ) := hres
  subst res
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (s * base : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, A, B, C,
                base]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [A, B, C, base] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, A, B, C, base] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  refine Ends.pieceThen (Ends.for (T := s*(countTime+jointTime maxMod+100)+20)
    (Q := Inv μ primes a b c nA nB nC q N aux s free s)
    (Inv μ primes a b c nA nB nC q N aux s free) s
    (countTime+jointTime maxMod+80) ?_ ?_ ?_ ?_ (hT := by first
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
                                                                | ((ring_nf); (omega))))) ?_
  · refine ⟨0,0,μ₀,?_,hkept₀⟩
    simp only [Inv,remaining_zero,update_frame_setLocal]
    exact congrArg (fun loc => (⟨loc,μ₀⟩ : State)) (frame_append_zeros _ 2).symm
  · rintro i _ hi _ ⟨jval,cval,ν,rfl,hkept⟩
    have hp := (hprime i hi).pos
    have hpmax : primes i ≤ maxMod :=
      (Nat.le_mul_of_pos_left (primes i) hq).trans (hproduct i hi)
    have hpword : (primes i : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hpmax).trans hmodword
    have hreadν : ν (aux+i) = (primes i : ℤ) := (hkept _ (by omega)).trans (hread i hi)
    have hnext := next_count_le_remaining (q := q) (nA := nA) (nB := nB) (nC := nC)
      primes A B C hi
    have hremaincast := remaining_succ_cast (q := q) (nA := nA) (nB := nB) (nC := nC)
      primes A B C hi
    have hscoreNext := hscoreZ (i+1)
    have hscoreNow := hscoreZ i
    dsimp [A,B,C] at hnext hremaincast hscoreNext hscoreNow
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
              ((joint_meets (d := d + 1) (q := q) (p := primes i) hjoint hem hw
                  (by omega) hq hp (hproduct i hi) hspace hjword)
                _ (by omega))
              ?_ ?_ ?_ ?_
        |
          refine
            Light.Ends.callToThen
              (joint_meets (d := d + 1) (q := q) (p := primes i) hjoint hem hw
                (by omega) hq hp (hproduct i hi) hspace hjword)
              ?_ ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hreadν,
                  A, B, C, base]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hreadν, A, B, C, base] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 => omega);
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hreadν, A, B, C, base] <;>
                omega)));
      (on_goal -1 =>
          ((rintro jres ν₁ ⟨hjres, hkeep₁⟩);
            (try with_unfolding_none refine Light.Ends.skip ?_)))
    subst jres
    have hkept₁ : Kept μ ν₁ free := fun j hj => (hkeep₁ j hj).trans (hkept j hj)
    have hjpos := joint_positive hq (hprime i hi)
    have hjmax := (joint_le_mul q (primes i) hp).trans (hproduct i hi)
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
              ((hcount ν₁ (joint q (primes i)) hkept₁ hjpos hjmax) _ (by omega)) ?_
              ?_ ?_ ?_
        |
          refine
            Light.Ends.callToThen
              (hcount ν₁ (joint q (primes i)) hkept₁ hjpos hjmax) ?_ ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, A, B, C,
                  base]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [A, B, C, base] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 => omega);
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, A, B, C, base] <;> omega)));
      (on_goal -1 =>
          ((rintro cres ν₂ ⟨hcres, hkeep₂⟩);
            (try with_unfolding_none refine Light.Ends.skip ?_)))
    subst cres
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
          Light.Ends.setToThen (remaining primes s q nA nB nC A B C (i + 1)) ?_ ?_
            ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, A, B, C,
                  base, hremaincast]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [A, B, C, base, hremaincast] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, A, B, C, base,
                  hremaincast] <;>
                omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    refine ⟨by simp, (joint q (primes i) : ℤ),
      (ModuloCounts.count (joint q (primes i)) nA nB nC A B C : ℤ),ν₂,?_,?_⟩
    · simp [Inv,update_frame_setLocal,A,B,C,base]
    · intro j hj
      exact (hkeep₂ j hj).trans (hkept₁ j hj)
  · intro σ _ hI
    exact hI
  · rintro i _ hi _ ⟨jval,cval,ν,rfl,hkept⟩
    simp
  · rintro σ ⟨jval,cval,ν,rfl,hkept⟩
    have hsc := hscoreZ s
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
          Light.Ends.setToThen (remaining primes s q nA nB nC A B C s) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, A, B, C,
                  base]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [A, B, C, base] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, A, B, C, base] <;> omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    exact ⟨by rw [score_eq_remaining primes s q nA nB nC A B C hprime hinj]; simp,hkept⟩


























































































































































end ThreeSum.LightWeightedScore

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain pCount pJoint pEmod : Nat},
  @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMain)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightWeightedScore.body pCount pJoint)) →
    @Eq.{1} (Option.{0} Light.Stmt)
        (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
          (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
          (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pJoint)
        (@Option.some.{0} Light.Stmt (ThreeSum.LightWeightedScore.jointBody pEmod)) →
      @Eq.{1} (Option.{0} Light.Stmt)
          (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
            (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
            (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pEmod)
          (@Option.some.{0} Light.Stmt Light.emodBody) →
        ∀ {μ : Nat → Int} {a b c nA nB nC q N aux s free maxMod countTime : Nat} (primes : Nat → Nat),
          @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
            @LT.lt.{0} Nat instLTNat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                lim.depth →
              @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q →
                @LE.le.{0} Nat instLENat q maxMod →
                  @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a nA) free →
                    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b nB)
                        free →
                      @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c nC)
                          free →
                        @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) aux s)
                            free →
                          @LE.le.{0} Nat instLENat N lim.space →
                            @LE.le.{0} Nat instLENat nA N →
                              @LE.le.{0} Nat instLENat nB N →
                                @LE.le.{0} Nat instLENat nC N →
                                  @LE.le.{0} Nat instLENat
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) free
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (Nat.log (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maxMod
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                      lim.space →
                                    @LE.le.{0} Int Int.instLEInt
                                        (@Nat.cast.{0} Int instNatCastInt
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) s
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  N (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) maxMod))
                                            (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))))
                                        lim.word →
                                      (∀ (i : Nat),
                                          @LT.lt.{0} Nat instLTNat i s →
                                            @Eq.{1} Int
                                              (μ
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) aux i))
                                              (@Nat.cast.{0} Int instNatCastInt (primes i))) →
                                        (∀ (i : Nat), @LT.lt.{0} Nat instLTNat i s → Nat.Prime (primes i)) →
                                          (∀ (i : Nat),
                                              @LT.lt.{0} Nat instLTNat i s →
                                                ∀ (j : Nat),
                                                  @LT.lt.{0} Nat instLTNat j s →
                                                    @Eq.{1} Nat (primes i) (primes j) → @Eq.{1} Nat i j) →
                                            (∀ (i : Nat),
                                                @LT.lt.{0} Nat instLTNat i s →
                                                  @LE.le.{0} Nat instLENat
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q
                                                      (primes i))
                                                    maxMod) →
                                              (∀ (ν : Nat → Int) (p : Nat),
                                                  Light.Kept μ ν free →
                                                    @LT.lt.{0} Nat instLTNat
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                                        p →
                                                      @LE.le.{0} Nat instLENat p maxMod →
                                                        Light.Meets lim P pCount
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) d
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1))))
                                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
                                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt b)
                                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt c)
                                                                (@List.cons.{0} Int
                                                                  (@Nat.cast.{0} Int instNatCastInt nA)
                                                                  (@List.cons.{0} Int
                                                                    (@Nat.cast.{0} Int instNatCastInt nB)
                                                                    (@List.cons.{0} Int
                                                                      (@Nat.cast.{0} Int instNatCastInt nC)
                                                                      (@List.cons.{0} Int
                                                                        (@Nat.cast.{0} Int instNatCastInt p)
                                                                        (@List.cons.{0} Int
                                                                          (@Nat.cast.{0} Int instNatCastInt N)
                                                                          (@List.cons.{0} Int
                                                                            (@Nat.cast.{0} Int instNatCastInt free)
                                                                            (@List.nil.{0} Int))))))))))
                                                          ν countTime fun (r : Int) (ν' : Nat → Int) =>
                                                          And
                                                            (@Eq.{1} Int r
                                                              (@Nat.cast.{0} Int instNatCastInt
                                                                (ThreeSum.ModuloCounts.count p nA nB nC
                                                                  (fun (j : Nat) =>
                                                                    μ
                                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                        (@instHAdd.{0} Nat instAddNat) a j))
                                                                  (fun (j : Nat) =>
                                                                    μ
                                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                        (@instHAdd.{0} Nat instAddNat) b j))
                                                                  fun (j : Nat) =>
                                                                  μ
                                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                      (@instHAdd.{0} Nat instAddNat) c j))))
                                                            (Light.Kept ν ν' free)) →
                                                Light.Meets lim P pMain d
                                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
                                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt b)
                                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt c)
                                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt nA)
                                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt nB)
                                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt nC)
                                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt q)
                                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt N)
                                                                  (@List.cons.{0} Int
                                                                    (@Nat.cast.{0} Int instNatCastInt aux)
                                                                    (@List.cons.{0} Int
                                                                      (@Nat.cast.{0} Int instNatCastInt s)
                                                                      (@List.cons.{0} Int
                                                                        (@Nat.cast.{0} Int instNatCastInt free)
                                                                        (@List.nil.{0} Int))))))))))))
                                                  μ (ThreeSum.LightWeightedScore.time countTime s maxMod)
                                                  fun (r : Int) (μ' : Nat → Int) =>
                                                  And
                                                    (@Eq.{1} Int r
                                                      (@Nat.cast.{0} Int instNatCastInt
                                                        (ThreeSum.WeightedScore.score primes s q nA nB nC
                                                          (fun (j : Nat) =>
                                                            μ
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat) a j))
                                                          (fun (j : Nat) =>
                                                            μ
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat) b j))
                                                          fun (j : Nat) =>
                                                          μ
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat) c j))))
                                                    (Light.Kept μ μ' free) := by
  exact @ThreeSum.LightWeightedScore.meets_of_count_backend_sourceProof

#print axioms solution
