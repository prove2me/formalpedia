-- Prove2me | solution 1 for ThreeSum.LightLocalCoverHost.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:37:33.742107+00:00
-- url     : https://prove2.me/submissions/ece79687-9118-4729-9b07-bfde73ae384b

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
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
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
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
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
import Mathlib.Data.List.Range
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
import Theorems.Thm_ThreeSum_LightCoverGreedy_Procs_meets
import Theorems.Thm_ThreeSum_LightLocalCoverMatrix_Procs_meets
import Theorems.Thm_ThreeSum_LightLocalCoverSchedule_indices_lt
import Theorems.Thm_ThreeSum_LightLocalCoverTables_Data_gathered_schedule
import Theorems.Thm_ThreeSum_LightLocalCoverTables_Data_of_kept
import Theorems.Thm_ThreeSum_LightWeightGather_Procs_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightLocalCoverTables
end ThreeSum.LightLocalCoverTables
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.LocalMaskGraph
end ThreeSum.LocalMaskGraph
namespace ThreeSum.LocalMaskHashes
end ThreeSum.LocalMaskHashes
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
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


/-! # Boolean-array semantics of the already specified finite greedy schedule -/

namespace ThreeSum.BooleanGreedy

open Finset
open scoped BigOperators











































































































theorem choices_length (matrix : ℕ → ℕ → ℕ) (rows cols t : ℕ) :
    (choices matrix rows cols t).length = t := Cover.greedyChoices_length ..




end ThreeSum.BooleanGreedy

end

section


/-!
# Ordered radix enumeration of local hash coefficients

The Cartesian-product list used by `allWeights` enumerates the first
coordinate most slowly. The radix index consequently stores that coordinate
in its most significant digit. The equality below is equality of lists,
including their order and repetitions, rather than a membership equivalence.
-/

namespace ThreeSum.WeightEnumeration

open LocalHashMoments

variable {ι K : Type*} [DecidableEq ι] [NatCast K]





























































































































































theorem decodedWeight_val (L p k : ℕ) (i : Fin L × Bool) :
    (decodedWeight (K := ZMod p) L p k i).val = digit p (2*L) k (coordinateIndex i) := by
  simp [decodedWeight,digit,ZMod.val_natCast]































end ThreeSum.WeightEnumeration

end

section


/-!
# Evaluating a one-hot hash from a subset mask

The executable recursion examines exactly one bit per level using a cached
power of two.  Its result is the sum of the selected symbol coefficients,
and is connected here to the raw hashes used by the global encoding.
-/

namespace ThreeSum.OneHotMask

open Finset SubsetAddress LocalHashMoments
open scoped BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

























































@[simp] theorem extend_fin {L : ℕ} (f : Fin L → ℕ) (i : Fin L) :
    extend f i.val = f i := by simp [extend, i.isLt]









































end ThreeSum.OneHotMask

end

section


/-! # A literal Boolean coordinate row for a subset mask -/

namespace ThreeSum.LightMaskBits

open Light LightSubsetAddress MaskErase



theorem bit_le (L m j : ℕ) : bit L m j ≤ 1 := by unfold bit; split <;> omega



























variable {lim : Limits} {P : Program} {d : ℕ}


























































































end ThreeSum.LightMaskBits

end

section


/-!
# Concrete integer indices for the local disjoint-subset graph

The finite list is the already checked layer-mask enumeration. Its Boolean
coordinate rows make disjointness an ordinary zero Boolean inner product.
-/

namespace ThreeSum.LocalMaskGraph

open Finset SubsetAddress MaskDecode
open scoped BigOperators












theorem maskAt_spec {L h i : ℕ} (hi : i < vertexCount L h) :
    IsMask L h (maskAt L h i) := (mem_enumerateLayer L h _).mp (maskAt_mem hi)






























































end ThreeSum.LocalMaskGraph

end

section


/-!
# The literal cover-matrix entry is the retained-edge predicate

This identifies the actual all-pairs, histogram-trimmed support table with
the same `Covers` relation used by the finite moment and greedy proof.
-/

namespace ThreeSum.LocalCoverMatrix

open Finset LocalHashMoments LocalCoverBounds LocalMaskGraph LocalMaskHashes

variable {h L k : ℕ}
















theorem entry_le (w : Weight L (LocalField h)) (k B r : ℕ) : entry w k B r ≤ 1 := by
  unfold entry LightSupportMark.bit
  split <;> omega




































































































end ThreeSum.LocalCoverMatrix

end

section


/-!
# Exact local schedule occurrence indices

The machine's Boolean matrix uses radix-indexed candidate rows and ordered
residue-pair columns. These changes of representation preserve the entire
original local schedule, including ties and repeated selected maps.
-/

namespace ThreeSum.LightLocalCoverSchedule

open Finset LocalHashMoments LocalCoverBounds GlobalEncoding












theorem rows_pos (h : ℕ) : 0 < rows h := Nat.pow_pos (localPrime_pos h)






























































theorem indices_length (h : ℕ) : (indices h).length = scheduleSize h :=
  BooleanGreedy.choices_length ..
















theorem candidateAt_lt (h : ℕ) (s : Occurrence h) : candidateAt h s < rows h := by
  have hs : s.val < (indices h).length := by rw [indices_length]; exact s.isLt
  unfold candidateAt
  rw [List.getD_eq_getElem _ _ hs]
  exact indices_lt h (List.getElem_mem hs)


















































end ThreeSum.LightLocalCoverSchedule

end

section


/-!
# Exact semantic interfaces for constructed local-cover tables

The concrete matrix constructor uses the unchanged radix enumeration of
the original local maps. Its retained histograms and gathered coefficient
rows are identified with the original occurrence-indexed encoding.
-/

namespace ThreeSum.LightLocalCoverTables

open Light LocalHashMoments LocalCoverBounds GlobalEncoding LightLocalCoverSchedule













theorem coeff_digit (h j : ℕ) (b : Bool) (i : Fin (512*h)) :
    LocalMaskHashes.coeff b (candidate h j) i.val =
      WeightEnumeration.digit (localPrime h) (2*(512*h)) j (2*i.val+(if b then 1 else 0)) := by
  simp only [LocalMaskHashes.coeff,OneHotMask.extend_fin,candidate,
    WeightEnumeration.decodedWeight_val,WeightEnumeration.coordinateIndex]








theorem Data.matrix_read {μ : ℕ → ℤ} {h maps hist0 hist1 matrixPtr : ℕ}
    (H : Data μ h maps hist0 hist1 matrixPtr) {j r : ℕ} (hj : j < rows h) (hr : r < cols h) :
    μ (matrixPtr+j*cols h+r) = (matrix h j r : ℤ) := (H j hj).2.2 r hr































































end ThreeSum.LightLocalCoverTables

end

section


/-!
# Constructing the exact local schedule and its retained tables

This fixed program constructs every candidate table, executes the unchanged
first-maximum greedy routine, and gathers the selected coefficient rows.
Its output contains the original schedule maps in exact occurrence order,
including ties and repetitions, and retains both candidate count tables.
-/

namespace ThreeSum.LightLocalCoverHost

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables

set_option maxHeartbeats 2000000
set_option maxRecDepth 6000




























variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets_sourceProof {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {h masks bitPtr maps raw0 raw1 hist0 hist1 matrixPtr work scheduleMaps : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+6 ≤ lim.depth)
    (hspace : LightLocalCoverCandidate.space work (512*h)
      (LocalMaskGraph.vertexCount (512*h) h) (localPrime h) ≤ lim.space)
    (hmasks : masks+LocalMaskGraph.vertexCount (512*h) h ≤ maps)
    (hbits : bitPtr+LocalMaskGraph.vertexCount (512*h) h*(512*h) ≤ maps)
    (hmaps : maps+rows h*(2*(512*h)) ≤ raw0)
    (hraw0 : raw0+2*LocalMaskGraph.vertexCount (512*h) h ≤ raw1)
    (hraw1 : raw1+2*LocalMaskGraph.vertexCount (512*h) h ≤ hist0)
    (hhist0 : hist0+rows h*localPrime h ≤ hist1)
    (hhist1 : hist1+rows h*localPrime h ≤ matrixPtr)
    (hmatrix : matrixPtr+rows h*cols h ≤ work)
    (hschedule : work+LightCoverGreedy.total (rows h) (cols h) (scheduleSize h) ≤ scheduleMaps)
    (houtSpace : scheduleMaps+scheduleSize h*(2*(512*h)) ≤ lim.space)
    (hword : (word h : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < LocalMaskGraph.vertexCount (512*h) h,
      μ (masks+i) = (LocalMaskGraph.maskAt (512*h) h i : ℤ))
    (hbitsRead : ∀ i < LocalMaskGraph.vertexCount (512*h) h, ∀ j < 512*h,
      μ (bitPtr+i*(512*h)+j) = (LocalCoverMatrix.bits (512*h) h i j : ℤ)) :
    Meets lim P pMain d
      [512*h,localPrime h,rows h,LocalMaskGraph.vertexCount (512*h) h,localBucketCap h,
        masks,bitPtr,maps,raw0,raw1,hist0,hist1,matrixPtr,work,scheduleSize h,scheduleMaps]
      μ (time h)
      (fun r ν => r = (scheduleMaps : ℤ) ∧
        Data ν h maps hist0 hist1 matrixPtr ∧ ScheduleRows ν h scheduleMaps ∧
        (∀ s : Occurrence h,
          ν (LightCoverGreedy.out work (rows h) (cols h)+s.val) = (candidateAt h s : ℤ)) ∧
        Kept μ ν maps) := by
  have hwork : work ≤ lim.space := by unfold LightLocalCoverCandidate.space at hspace; omega
  have hscheduleWork : work ≤ scheduleMaps := by omega
  have hbudget (x : ℕ) (hx : x ≤ word h) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hmatrixWord := hbudget
    (LightLocalCoverCandidate.word (512*h) (LocalMaskGraph.vertexCount (512*h) h)
      (localPrime h) (localBucketCap h) (rows h)) (by unfold word; omega)
  have hgatherWord := hbudget
    (LightWeightGather.word (rows h) (scheduleSize h) (2*(512*h))) (by unfold word; omega)
  have hLWord := hbudget (512*h) (by unfold word LightWeightGather.word; omega)
  have hWWord := hbudget (2*(512*h)) (by unfold word LightWeightGather.word; omega)
  have hWWordZ : (2 : ℤ)*(512*(h : ℤ)) ≤ lim.word := by exact_mod_cast hWWord
  have h2Word := hbudget 2 (by
    unfold word LightLocalCoverCandidate.word LightPairFlags.word
    omega)
  have hpWord := hbudget (localPrime h) (by
    unfold word LightLocalCoverCandidate.word LightPairFlags.word
    omega)
  have hp2Word := hbudget (localPrime h*localPrime h) (by
    unfold word LightLocalCoverCandidate.word LightPairFlags.word
    omega)
  have hp2WordZ : (localPrime h : ℤ)*localPrime h ≤ lim.word := by exact_mod_cast hp2Word
  have hNWord := hbudget (rows h) (by unfold word LightWeightGather.word; omega)
  have hTWord := hbudget (scheduleSize h) (by unfold word LightWeightGather.word; omega)
  have hnWord := hbudget (LocalMaskGraph.vertexCount (512*h) h) (by
    unfold word LightLocalCoverCandidate.word LightPairFlags.word
    omega)
  have hcapWord := hbudget (localBucketCap h) (by
    unfold word LightLocalCoverCandidate.word LightPairFlags.word
    omega)
  have hn : 0 < LocalMaskGraph.vertexCount (512*h) h := Nat.choose_pos (by omega)
  have hmapsWork : maps+rows h*(2*(512*h)) ≤ work := by omega
  have hhist0Work : hist0+rows h*localPrime h ≤ work := by omega
  have hhist1Work : hist1+rows h*localPrime h ≤ work := by omega
  have hgreedySpace : work+LightCoverGreedy.total (rows h) (cols h) (scheduleSize h) ≤ lim.space := by omega
  have houtEnd : LightCoverGreedy.out work (rows h) (cols h)+scheduleSize h ≤ scheduleMaps := by
    unfold LightCoverGreedy.out LightCoverGreedy.total at *
    omega
  have hm := S.matrix.meets (d := d+1) (μ := μ) (L := 512*h)
    (n := LocalMaskGraph.vertexCount (512*h) h) (p := localPrime h) (cap := localBucketCap h)
    (N := rows h) (masks := masks) (bitPtr := bitPtr) (maps := maps) (raw0 := raw0)
    (raw1 := raw1) (hist0 := hist0) (hist1 := hist1) (dst := matrixPtr) (work := work)
    (LocalMaskGraph.maskAt (512*h) h) (LocalCoverMatrix.bits (512*h) h)
    (fun j => LocalMaskHashes.coeff false (candidate h j))
    (fun j => LocalMaskHashes.coeff true (candidate h j))
    hw (by omega) (localPrime_pos h) hn hspace hmasks hbits hmaps hraw0 hraw1 hhist0 hhist1
    hmatrix hmatrixWord hmaskRead (fun _ hi => (LocalMaskGraph.maskAt_spec hi).1) hbitsRead
    (fun i _ j _ => LightMaskBits.bit_le (512*h) (LocalMaskGraph.maskAt (512*h) h i) j)
    (by intro j _ i hi; simpa only [Bool.false_eq_true,ite_false,Nat.add_zero] using coeff_digit h j false ⟨i,hi⟩)
    (by intro j _ i hi; simpa only [ite_true] using coeff_digit h j true ⟨i,hi⟩)
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
    (first
      | refine Light.Ends.callToThen (hm _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hm ?_ ?_ ?_ ?_);
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
        ((rintro vm μ₁ ⟨hdata₁, hkeep₁⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have H₁ : Data μ₁ h maps hist0 hist1 matrixPtr := hdata₁
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (localPrime h * localPrime h : ℕ) ?_ ?_ ?_);
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
  have hg := S.greedy.meets (d := d+1) (μ := μ₁) (src := matrixPtr) (activePtr := work)
    (rows := rows h) (cols := cols h) (rounds := scheduleSize h) (LightLocalCoverSchedule.matrix h)
    hw (by omega) (rows_pos h) hmatrix hgreedySpace
    (fun _ hi _ hr => H₁.matrix_read hi hr) (fun _ _ _ _ => LocalCoverMatrix.entry_le ..) (by omega)
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
      | refine Light.Ends.callToThen (hg _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hg ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time,
                cols]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [time, cols] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, time, cols] <;> omega)));
    (on_goal -1 =>
        ((rintro vg μ₂ ⟨hvg, hchoices, hactive, hkeep₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have H₂ : Data μ₂ h maps hist0 hist1 matrixPtr :=
    H₁.of_kept (fun a ha => hkeep₂ a (Or.inl ha)) hmapsWork hhist0Work hhist1Work hmatrix
  have hselection : ∀ s < scheduleSize h,
      μ₂ (LightCoverGreedy.out work (rows h) (cols h)+s) = ((indices h).getD s 0 : ℤ) := by
    intro s hs
    have hs' : s < (indices h).length := by rw [indices_length]; exact hs
    have hr := hchoices s (by simpa only [List.length_map,BooleanGreedy.choices_length] using hs)
    rw [List.getD_eq_getElem _ _ hs']
    simpa only [List.getElem_map,indices] using hr
  have hselectionLt : ∀ s < scheduleSize h, (indices h).getD s 0 < rows h := by
    intro s hs
    exact candidateAt_lt h ⟨s,hs⟩
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (2 * (512 * h) : ℕ) ?_ ?_ ?_);
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
  have hc := S.gather.meets (d := d+1) (μ := μ₂)
    (indices := LightCoverGreedy.out work (rows h) (cols h)) (src := maps) (dst := scheduleMaps)
    (N := rows h) (rows := scheduleSize h) (width := 2*(512*h)) (fun s => (indices h).getD s 0)
    hw (by omega) houtEnd (by omega) houtSpace hgatherWord hselectionLt hselection
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
                hvg, LightCoverGreedy.out, cols]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [time, hvg, LightCoverGreedy.out, cols] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, time, hvg,
                LightCoverGreedy.out, cols] <;>
              omega)));
    (on_goal -1 =>
        ((rintro vc μ₃ ⟨hcopy, hkeep₃⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have H₃ : Data μ₃ h maps hist0 hist1 matrixPtr :=
    H₂.of_kept (fun a ha => hkeep₃ a (Or.inl (by omega))) hmapsWork hhist0Work hhist1Work hmatrix
  have hrows₃ : ScheduleRows μ₃ h scheduleMaps := H₂.gathered_schedule hcopy
  have hselection₃ : ∀ s : Occurrence h,
      μ₃ (LightCoverGreedy.out work (rows h) (cols h)+s.val) = (candidateAt h s : ℤ) := by
    intro s
    rw [hkeep₃ _ (Or.inl (by have hs := s.isLt; omega))]
    exact hselection s.val s.isLt
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (scheduleMaps : ℕ) ?_ ?_ ?_);
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
  refine ⟨rfl,H₃,hrows₃,hselection₃,?_⟩
  intro a ha
  change μ₃ a = μ a
  rw [hkeep₃ a (Or.inl (by omega)),hkeep₂ a (Or.inl (by omega))]
  exact hkeep₁ a ha

















end ThreeSum.LightLocalCoverHost

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (S : ThreeSum.LightLocalCoverHost.Procs P pMain)
  {μ : Nat → Int} {h masks bitPtr maps raw0 raw1 hist0 hist1 matrixPtr work scheduleMaps : Nat},
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
        lim.depth →
      @LE.le.{0} Nat instLENat
          (ThreeSum.LightLocalCoverCandidate.space work
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
            (ThreeSum.LocalMaskGraph.vertexCount
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
              h)
            (ThreeSum.LocalCoverBounds.localPrime h))
          lim.space →
        @LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) masks
              (ThreeSum.LocalMaskGraph.vertexCount
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                h))
            maps →
          @LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bitPtr
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (ThreeSum.LocalMaskGraph.vertexCount
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                    h)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
              maps →
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (ThreeSum.LightLocalCoverSchedule.rows h)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
                raw0 →
              @LE.le.{0} Nat instLENat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) raw0
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (ThreeSum.LocalMaskGraph.vertexCount
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                        h)))
                  raw1 →
                @LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) raw1
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (ThreeSum.LocalMaskGraph.vertexCount
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                          h)))
                    hist0 →
                  @LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) hist0
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (ThreeSum.LightLocalCoverSchedule.rows h) (ThreeSum.LocalCoverBounds.localPrime h)))
                      hist1 →
                    @LE.le.{0} Nat instLENat
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) hist1
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (ThreeSum.LightLocalCoverSchedule.rows h) (ThreeSum.LocalCoverBounds.localPrime h)))
                        matrixPtr →
                      @LE.le.{0} Nat instLENat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) matrixPtr
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (ThreeSum.LightLocalCoverSchedule.rows h) (ThreeSum.LightLocalCoverSchedule.cols h)))
                          work →
                        @LE.le.{0} Nat instLENat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
                              (ThreeSum.LightCoverGreedy.total (ThreeSum.LightLocalCoverSchedule.rows h)
                                (ThreeSum.LightLocalCoverSchedule.cols h) (ThreeSum.GlobalEncoding.scheduleSize h)))
                            scheduleMaps →
                          @LE.le.{0} Nat instLENat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) scheduleMaps
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (ThreeSum.GlobalEncoding.scheduleSize h)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
                              lim.space →
                            @LE.le.{0} Int Int.instLEInt
                                (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightLocalCoverHost.word h)) lim.word →
                              (∀ (i : Nat),
                                  @LT.lt.{0} Nat instLTNat i
                                      (ThreeSum.LocalMaskGraph.vertexCount
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                        h) →
                                    @Eq.{1} Int
                                      (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) masks i))
                                      (@Nat.cast.{0} Int instNatCastInt
                                        (ThreeSum.LocalMaskGraph.maskAt
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                          h i))) →
                                (∀ (i : Nat),
                                    @LT.lt.{0} Nat instLTNat i
                                        (ThreeSum.LocalMaskGraph.vertexCount
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                          h) →
                                      ∀ (j : Nat),
                                        @LT.lt.{0} Nat instLTNat j
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h) →
                                          @Eq.{1} Int
                                            (μ
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bitPtr
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512)))
                                                      h)))
                                                j))
                                            (@Nat.cast.{0} Int instNatCastInt
                                              (ThreeSum.LocalCoverMatrix.bits
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                                h i j))) →
                                  Light.Meets lim P pMain d
                                    (@List.cons.{0} Int
                                      (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                                        (@OfNat.ofNat.{0} Int (nat_lit 512) (@instOfNat (nat_lit 512)))
                                        (@Nat.cast.{0} Int instNatCastInt h))
                                      (@List.cons.{0} Int
                                        (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LocalCoverBounds.localPrime h))
                                        (@List.cons.{0} Int
                                          (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightLocalCoverSchedule.rows h))
                                          (@List.cons.{0} Int
                                            (@Nat.cast.{0} Int instNatCastInt
                                              (ThreeSum.LocalMaskGraph.vertexCount
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                                h))
                                            (@List.cons.{0} Int
                                              (@Nat.cast.{0} Int instNatCastInt
                                                (ThreeSum.LocalCoverBounds.localBucketCap h))
                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt masks)
                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt bitPtr)
                                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt maps)
                                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt raw0)
                                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt raw1)
                                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt hist0)
                                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt hist1)
                                                            (@List.cons.{0} Int
                                                              (@Nat.cast.{0} Int instNatCastInt matrixPtr)
                                                              (@List.cons.{0} Int
                                                                (@Nat.cast.{0} Int instNatCastInt work)
                                                                (@List.cons.{0} Int
                                                                  (@Nat.cast.{0} Int instNatCastInt
                                                                    (ThreeSum.GlobalEncoding.scheduleSize h))
                                                                  (@List.cons.{0} Int
                                                                    (@Nat.cast.{0} Int instNatCastInt scheduleMaps)
                                                                    (@List.nil.{0} Int)))))))))))))))))
                                    μ (ThreeSum.LightLocalCoverHost.time h) fun (r : Int) (ν : Nat → Int) =>
                                    And (@Eq.{1} Int r (@Nat.cast.{0} Int instNatCastInt scheduleMaps))
                                      (And (ThreeSum.LightLocalCoverTables.Data ν h maps hist0 hist1 matrixPtr)
                                        (And (ThreeSum.LightLocalCoverTables.ScheduleRows ν h scheduleMaps)
                                          (And
                                            (∀ (s : ThreeSum.GlobalEncoding.Occurrence h),
                                              @Eq.{1} Int
                                                (ν
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (ThreeSum.LightCoverGreedy.out work
                                                      (ThreeSum.LightLocalCoverSchedule.rows h)
                                                      (ThreeSum.LightLocalCoverSchedule.cols h))
                                                    (@Fin.val (ThreeSum.GlobalEncoding.scheduleSize h) s)))
                                                (@Nat.cast.{0} Int instNatCastInt
                                                  (ThreeSum.LightLocalCoverSchedule.candidateAt h s)))
                                            (Light.Kept μ ν maps)))) := by
  exact @ThreeSum.LightLocalCoverHost.Procs.meets_sourceProof

#print axioms solution
