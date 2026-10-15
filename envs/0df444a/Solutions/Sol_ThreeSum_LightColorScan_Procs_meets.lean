-- Prove2me | solution 1 for ThreeSum.LightColorScan.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:04:08.333087+00:00
-- url     : https://prove2.me/submissions/08502495-79de-40c0-b30f-458b57662538

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
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
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
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_LightColorParameters_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.ColorParameters
end ThreeSum.ColorParameters
namespace ThreeSum.ColorScan
end ThreeSum.ColorScan

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
# A literal small coloring-parameter order

There are exactly 81*W² integer slots. Four ternary digits select the
color map, and the remaining quotient selects its two binary coordinates.
The inverse code proves that every separating parameter is present.
-/

namespace ThreeSum.ColorParameters

































theorem fields_parameter {W t : ℕ} (ht : t < count W) : fields (parameter ht)=data W t := rfl

























































end ThreeSum.ColorParameters

end

section


/-! # Correctness of a prefix of the literal coloring family -/

namespace ThreeSum.ColorScan

open ColorParameters




theorem hit_zero {n W : ℕ} (x : Fin n → ℤ) : ¬ Hit x W 0 := by
  rintro ⟨i,hi,hlt,_⟩
  omega

theorem hit_mono {n W a b : ℕ} {x : Fin n → ℤ} (hab : a ≤ b) :
    Hit x W a → Hit x W b := by
  rintro ⟨i,hi,hlt,hx⟩
  exact ⟨i,hi,hlt.trans_le hab,hx⟩

theorem hit_succ {n W t : ℕ} (x : Fin n → ℤ) (ht : t < count W) :
    Hit x W (t+1) ↔ Hit x W t ∨ ColorClassLists.witness (parameter ht) x := by
  constructor
  · rintro ⟨i,hi,hlt,hx⟩
    by_cases he : i=t
    · subst i
      exact Or.inr hx
    · exact Or.inl ⟨i,hi,by omega,hx⟩
  · rintro (⟨i,hi,hlt,hx⟩ | hx)
    · exact ⟨i,hi,by omega,hx⟩
    · exact ⟨t,ht,by omega,hx⟩










end ThreeSum.ColorScan

end

section


/-!
# Execute the finite coloring search

The recursive driver reuses one six-cell parameter row and all subsequent
per-color scratch. Once a color accepts, later color calls are skipped.
This is a compositional execution theorem: the concrete selected-color
decision procedure must supply the explicit per-color call contract below.
It does not assert existence of that still-being-integrated solver.
-/

namespace ThreeSum.LightColorScan

open Light ColorParameters ColorScan

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
























variable {lim : Limits} {P : Program}

theorem Procs.meets_sourceProof {pMain src n params free W colorTime colorDepth : ℕ}
    (R : Procs P pMain) (x : Fin n → ℤ) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : free+6 ≤ lim.space) (hsrc : src ≤ free) (hparams : params ≤ free)
    (hword : ((n+count W+W+100 : ℕ) : ℤ) ≤ lim.word)
    (hcolor : ∀ (i : ℕ) (hi : i < count W) (ν : ℕ → ℤ),
      Kept μ ν free → Seg ν free (fields (parameter hi)) →
      ∀ dd : ℕ, dd+colorDepth ≤ lim.depth →
      Meets lim P R.pColor dd [src,n,params,free,free+6] ν colorTime
        (fun r ξ => (r=0 ∨ r=1) ∧
          (r=1 ↔ ColorClassLists.witness (parameter hi) x) ∧ Kept ν ξ free))
    {t d : ℕ} {ν : ℕ → ℤ} (ht : t ≤ count W)
    (hd : d+t+colorDepth+3 ≤ lim.depth) (hkeep : Kept μ ν free) :
    Meets lim P pMain d [src,n,params,free,W,t] ν (time colorTime W t)
      (fun r ξ => (r=0 ∨ r=1) ∧ (r=1 ↔ Hit x W t) ∧ Kept ν ξ free) := by
  have hsmall (a : ℕ) (ha : a ≤ n+count W+W+100) : (a : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ha).trans hword
  have htwo := hsmall 2 (by omega)
  have hW := hsmall W (by omega)
  have hcount := hsmall (count W) (by omega)
  have hn := hsmall n (by omega)
  induction t generalizing d ν with
  | zero =>
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
        (refine
            Light.Ends.iteIffThen ((0 : ℤ) < 0) (fun hbad => ?_) (fun hno => ?_) ?_
              ?_);
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
        (all_goals
            repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)
      · omega
      · focus
           ((((first
                   | refine Light.Ends.seqSelf ?_
                   | refine Light.Ends.skipLast ?_));
               (repeat
                   with_unfolding_none
                     first
                     | refine Light.Ends.seqAssoc ?_
                     | refine Light.Ends.skipThen ?_)));
           (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
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
        exact ⟨by simp,by simp [hit_zero],SameOn.refl⟩
  | succ t ih =>
      have ht' : t < count W := by omega
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
        (refine
            Light.Ends.iteIffThen ((0 : ℤ) < ((t + 1 : ℕ) : ℤ)) (fun hyes => ?_)
              (fun hbad => ?_) ?_ ?_);
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
        (all_goals
            repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)
      · have hrec := ih (d := d+1) (ν := ν) (by omega) (by omega) hkeep
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
            | refine Light.Ends.callToThen (hrec _ (by omega)) ?_ ?_ ?_ ?_
            | refine Light.Ends.callToThen hrec ?_ ?_ ?_ ?_);
          (on_goal -1 =>
              first
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
                    | ((ring_nf); (omega))));
          (on_goal -1 => omega);
          (on_goal -1 =>
              (((try have := Light.Std.space_le (by assumption)));
                ((try have := Light.Std.const_le (by assumption)));
                (simp [Light.Limits.Addr, abs_le, -abs_mul, time] <;> omega)));
          (on_goal -1 =>
              ((rintro prev ν₁ ⟨hprevBool, hprev, hkeep₁⟩);
                (try with_unfolding_none refine Light.Ends.skip ?_)))
        have hprevRange : 0 ≤ prev ∧ prev ≤ 1 := by rcases hprevBool with hh | hh <;> omega
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
              Light.Ends.iteIffThen ((0 : ℤ) < prev) (fun hhit => ?_) (fun hmiss => ?_)
                ?_ ?_);
          (on_goal -1 =>
              first
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
                    | ((ring_nf); (omega))));
          (on_goal -1 =>
              (((try have := Light.Std.space_le (by assumption)));
                ((try have := Light.Std.const_le (by assumption)));
                (simp [Light.Limits.Addr, abs_le, -abs_mul, time] <;> omega)));
          (all_goals
              repeat
                with_unfolding_none
                  first
                  | refine Light.Ends.seqAssoc ?_
                  | refine Light.Ends.skipThen ?_)
        · have hh := hit_mono (by omega : t ≤ t+1) (hprev.mp (by omega))
          focus
            ((((first
                    | refine Light.Ends.seqSelf ?_
                    | refine Light.Ends.skipLast ?_));
                (repeat
                    with_unfolding_none
                      first
                      | refine Light.Ends.seqAssoc ?_
                      | refine Light.Ends.skipThen ?_)));
            (refine Light.Ends.setToThen (1 : ℕ) ?_ ?_ ?_);
            (on_goal -1 =>
                first
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
                      | ((ring_nf); (omega))));
            (on_goal -1 =>
                (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, time] <;> omega)));
            (try with_unfolding_none refine Light.Ends.skip ?_)
          exact ⟨by simp,by simpa using hh,hkeep₁⟩
        · have hnoHit : ¬ Hit x W t := fun hh => hmiss (by have := hprev.mpr hh; omega)
          focus
            ((((first
                    | refine Light.Ends.seqSelf ?_
                    | refine Light.Ends.skipLast ?_));
                (repeat
                    with_unfolding_none
                      first
                      | refine Light.Ends.seqAssoc ?_
                      | refine Light.Ends.skipThen ?_)));
            (refine Light.Ends.setToThen (t : ℕ) ?_ ?_ ?_);
            (on_goal -1 =>
                first
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
                      | ((ring_nf); (omega))));
            (on_goal -1 =>
                (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, time] <;> omega)));
            (try with_unfolding_none refine Light.Ends.skip ?_)
          have hp := LightColorParameters.meets (d := d+1) (W := W) (t := t) (free := free)
            (μ := ν₁) R.parameters R.divide hw hspace (hsmall _ (by omega)) (by omega)
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
              | refine Light.Ends.callToThen (hp _ (by omega)) ?_ ?_ ?_ ?_
              | refine Light.Ends.callToThen hp ?_ ?_ ?_ ?_);
            (on_goal -1 =>
                first
                |
                  ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time,
                        LightColorParameters.time]);
                    (first
                      | omega
                      | ((ring_nf); (omega))))
                | omega
                |
                  (simp [time, LightColorParameters.time] <;>
                      first
                      | omega
                      | ((ring_nf); (omega))));
            (on_goal -1 => omega);
            (on_goal -1 =>
                (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, time,
                        LightColorParameters.time] <;>
                      omega)));
            (on_goal -1 =>
                ((rintro row ν₂ ⟨hrow, hdata, hkeep₂⟩);
                  (try with_unfolding_none refine Light.Ends.skip ?_)))
          have hrowData : Seg ν₂ free (fields (parameter ht')) := by
            simpa only [fields_parameter] using hdata
          have hkeepBefore : Kept ν₁ ν₂ free := fun i hi => hkeep₂ i (Or.inl hi)
          have htotal : Kept μ ν₂ free := fun i hi =>
            (hkeepBefore i hi).trans ((hkeep₁ i hi).trans (hkeep i hi))
          have hc := hcolor t ht' ν₂ htotal hrowData (d+1) (by omega)
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
                        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time,
                        LightColorParameters.time]);
                    (first
                      | omega
                      | ((ring_nf); (omega))))
                | omega
                |
                  (simp [time, LightColorParameters.time] <;>
                      first
                      | omega
                      | ((ring_nf); (omega))));
            (on_goal -1 => omega);
            (on_goal -1 =>
                (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, time,
                        LightColorParameters.time] <;>
                      omega)));
            (on_goal -1 =>
                ((rintro result ξ ⟨hbool, hresult, hkeep₃⟩);
                  (try with_unfolding_none refine Light.Ends.skip ?_)))
          have hrange : 0 ≤ result ∧ result ≤ 1 := by rcases hbool with hh | hh <;> omega
          focus
            ((((first
                    | refine Light.Ends.seqSelf ?_
                    | refine Light.Ends.skipLast ?_));
                (repeat
                    with_unfolding_none
                      first
                      | refine Light.Ends.seqAssoc ?_
                      | refine Light.Ends.skipThen ?_)));
            (refine Light.Ends.setToThen result ?_ ?_ ?_);
            (on_goal -1 =>
                first
                |
                  ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time,
                        LightColorParameters.time]);
                    (first
                      | omega
                      | ((ring_nf); (omega))))
                | omega
                |
                  (simp [time, LightColorParameters.time] <;>
                      first
                      | omega
                      | ((ring_nf); (omega))));
            (on_goal -1 =>
                (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, time,
                        LightColorParameters.time] <;>
                      omega)));
            (try with_unfolding_none refine Light.Ends.skip ?_)
          refine ⟨hbool,?_,?_⟩
          · rw [hit_succ x ht',or_iff_right hnoHit]
            exact hresult
          · intro i hi
            exact (hkeep₃ i hi).trans ((hkeepBefore i hi).trans (hkeep₁ i hi))
      · omega

end ThreeSum.LightColorScan

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {pMain src n params free W colorTime colorDepth : Nat}
  (R : ThreeSum.LightColorScan.Procs P pMain) (x : Fin n → Int) (μ : Nat → Int),
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) free
          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
        lim.space →
      @LE.le.{0} Nat instLENat src free →
        @LE.le.{0} Nat instLENat params free →
          @LE.le.{0} Int Int.instLEInt
              (@Nat.cast.{0} Int instNatCastInt
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (ThreeSum.ColorParameters.count W))
                    W)
                  (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100)))))
              lim.word →
            (∀ (i : Nat) (hi : @LT.lt.{0} Nat instLTNat i (ThreeSum.ColorParameters.count W)) (ν : Nat → Int),
                Light.Kept μ ν free →
                  Light.Seg ν free (@ThreeSum.ColorParameters.fields W (@ThreeSum.ColorParameters.parameter W i hi)) →
                    ∀ (dd : Nat),
                      @LE.le.{0} Nat instLENat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dd colorDepth) lim.depth →
                        Light.Meets lim P (@ThreeSum.LightColorScan.Procs.pColor P pMain R) dd
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt params)
                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt free)
                                  (@List.cons.{0} Int
                                    (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                                      (@Nat.cast.{0} Int instNatCastInt free)
                                      (@OfNat.ofNat.{0} Int (nat_lit 6) (@instOfNat (nat_lit 6))))
                                    (@List.nil.{0} Int))))))
                          ν colorTime fun (r : Int) (ξ : Nat → Int) =>
                          And
                            (Or (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
                              (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                            (And
                              (Iff (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                (@ThreeSum.ColorClassLists.witness n W (@ThreeSum.ColorParameters.parameter W i hi) x))
                              (Light.Kept ν ξ free))) →
              ∀ {t d : Nat} {ν : Nat → Int},
                @LE.le.{0} Nat instLENat t (ThreeSum.ColorParameters.count W) →
                  @LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d t) colorDepth)
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      lim.depth →
                    Light.Kept μ ν free →
                      Light.Meets lim P pMain d
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt params)
                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt free)
                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt W)
                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt t) (@List.nil.{0} Int)))))))
                        ν (ThreeSum.LightColorScan.time colorTime W t) fun (r : Int) (ξ : Nat → Int) =>
                        And
                          (Or (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
                            (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                          (And
                            (Iff (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              (@ThreeSum.ColorScan.Hit n x W t))
                            (Light.Kept ν ξ free)) := by
  exact @ThreeSum.LightColorScan.Procs.meets_sourceProof

#print axioms solution
