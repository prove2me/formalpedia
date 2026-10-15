-- Prove2me | solution 1 for ThreeSum.LightLocalCoverBuild.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:41:23.867427+00:00
-- url     : https://prove2.me/submissions/27d60011-30d9-4a0d-ba55-f7f4b2cb7b6b

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
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
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
import Theorems.Thm_ThreeSum_LightLocalCoverHost_Procs_meets
import Theorems.Thm_ThreeSum_LightMaskBitTable_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_meets


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
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
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
# A complete local-cover construction from the initialized parameters

The enumerated local vertices and their Boolean coordinate rows are built
inside this program. It then constructs all candidate tables, executes the
original greedy schedule, and gathers the exact occurrence coefficient
rows. There are no supplied mask, coefficient, histogram, or matrix tables.
-/

namespace ThreeSum.LightLocalCoverBuild

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables

set_option maxHeartbeats 1500000
set_option maxRecDepth 6000





























variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets_sourceProof {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {h masks bitPtr maps raw0 raw1 hist0 hist1 matrixPtr work scheduleMaps : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+7 ≤ lim.depth)
    (hspace : LightLocalCoverCandidate.space work (512*h)
      (LocalMaskGraph.vertexCount (512*h) h) (localPrime h) ≤ lim.space)
    (hmasks : masks+LocalMaskGraph.vertexCount (512*h) h ≤ bitPtr)
    (hbits : bitPtr+LocalMaskGraph.vertexCount (512*h) h*(512*h) ≤ maps)
    (hmaps : maps+rows h*(2*(512*h)) ≤ raw0)
    (hraw0 : raw0+2*LocalMaskGraph.vertexCount (512*h) h ≤ raw1)
    (hraw1 : raw1+2*LocalMaskGraph.vertexCount (512*h) h ≤ hist0)
    (hhist0 : hist0+rows h*localPrime h ≤ hist1)
    (hhist1 : hist1+rows h*localPrime h ≤ matrixPtr)
    (hmatrix : matrixPtr+rows h*cols h ≤ work)
    (hschedule : work+LightCoverGreedy.total (rows h) (cols h) (scheduleSize h) ≤ scheduleMaps)
    (houtSpace : scheduleMaps+scheduleSize h*(2*(512*h)) ≤ lim.space)
    (hword : (word h : ℤ) ≤ lim.word) :
    Meets lim P pMain d
      [512*h,h,localPrime h,rows h,LocalMaskGraph.vertexCount (512*h) h,localBucketCap h,
        masks,bitPtr,maps,raw0,raw1,hist0,hist1,matrixPtr,work,scheduleSize h,scheduleMaps]
      μ (time h)
      (fun r ν => r = (scheduleMaps : ℤ) ∧
        Data ν h maps hist0 hist1 matrixPtr ∧ ScheduleRows ν h scheduleMaps ∧
        (∀ s : Occurrence h,
          ν (LightCoverGreedy.out work (rows h) (cols h)+s.val) = (candidateAt h s : ℤ)) ∧
        Kept μ ν masks) := by
  have hwork : work ≤ lim.space := by unfold LightLocalCoverCandidate.space at hspace; omega
  have hpowSpace : work+(512*h+1) ≤ lim.space := by
    unfold LightLocalCoverCandidate.space at hspace
    omega
  have hmaskWork : masks+LocalMaskGraph.vertexCount (512*h) h ≤ work := by omega
  have hbitsWork : bitPtr+LocalMaskGraph.vertexCount (512*h) h*(512*h) ≤ work := by omega
  have hhostWord : (LightLocalCoverHost.word h : ℤ) ≤ lim.word := by
    have hb : LightLocalCoverHost.word h ≤ word h := Nat.le_add_right ..
    exact (Int.ofNat_le.mpr hb).trans hword
  have hpowerWord : ((2^(512*h+1) : ℕ) : ℤ) ≤ lim.word := by
    have hb : 2^(512*h+1) ≤ word h := Nat.le_add_left ..
    exact (Int.ofNat_le.mpr hb).trans hword
  have hbudget (x : ℕ) (hx : x ≤ LightLocalCoverHost.word h) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hhostWord
  have hLWord := hbudget (512*h) (by unfold LightLocalCoverHost.word LightWeightGather.word; omega)
  have hhWord : (h : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : h ≤ 512*h)).trans hLWord
  have hnWord := hbudget (LocalMaskGraph.vertexCount (512*h) h) (by
    unfold LightLocalCoverHost.word LightLocalCoverCandidate.word LightPairFlags.word
    omega)
  have hpWord := hbudget (localPrime h) (by
    unfold LightLocalCoverHost.word LightLocalCoverCandidate.word LightPairFlags.word
    omega)
  have hcapWord := hbudget (localBucketCap h) (by
    unfold LightLocalCoverHost.word LightLocalCoverCandidate.word LightPairFlags.word
    omega)
  have hNWord := hbudget (rows h) (by unfold LightLocalCoverHost.word LightWeightGather.word; omega)
  have hTWord := hbudget (scheduleSize h) (by unfold LightLocalCoverHost.word LightWeightGather.word; omega)
  apply Meets.of_body S.main
  unfold body time
  have he := LightSubsetEnumerationSetup.meets (d := d+1) (μ := μ) (L := 512*h) (k := h)
    (dst := masks) (work := work) S.enum S.powers S.enumRec hw hpowSpace hpowerWord
    (by omega) hmaskWork (by omega)
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
      | refine Light.Ends.callToThen (he _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen he ?_ ?_ ?_ ?_);
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
        ((rintro ve μ₁ ⟨hve, hmaskSeg, hpowers, hkeep₁⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hmaskRead₁ : ∀ i < LocalMaskGraph.vertexCount (512*h) h,
      μ₁ (masks+i) = (LocalMaskGraph.maskAt (512*h) h i : ℤ) := by
    intro i hi
    have hi' : i < (SubsetAddress.enumerateLayer (512*h) h).length := by
      simpa only [SubsetAddress.enumerateLayer_length,LocalMaskGraph.vertexCount] using hi
    have he := hmaskSeg i (by simpa only [List.length_map] using hi')
    simpa only [LocalMaskGraph.maskAt,List.getD_eq_getElem _ _ hi',List.getElem_map] using he
  have hmaskLt : ∀ i < LocalMaskGraph.vertexCount (512*h) h,
      LocalMaskGraph.maskAt (512*h) h i < 2^(512*h) := fun _ hi => (LocalMaskGraph.maskAt_spec hi).1
  have hb := LightMaskBitTable.meets (d := d+1) (μ := μ₁) (L := 512*h) (masks := masks)
    (dst := bitPtr) (n := LocalMaskGraph.vertexCount (512*h) h) (work := work)
    S.bits S.oneBits S.powers S.erase (LocalMaskGraph.maskAt (512*h) h)
    hw (by omega) hpowSpace hmasks hbitsWork hpowerWord hmaskRead₁ hmaskLt
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
      | refine Light.Ends.callToThen (hb _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hb ?_ ?_ ?_ ?_);
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
        ((rintro vb μ₂ ⟨hbitsRead, hkeep₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hmaskRead₂ : ∀ i < LocalMaskGraph.vertexCount (512*h) h,
      μ₂ (masks+i) = (LocalMaskGraph.maskAt (512*h) h i : ℤ) := by
    intro i hi
    rw [hkeep₂ _ ⟨by omega,Or.inl (by omega)⟩]
    exact hmaskRead₁ i hi
  have hh := S.host.meets (d := d+1) (μ := μ₂) (h := h) (masks := masks) (bitPtr := bitPtr)
    (maps := maps) (raw0 := raw0) (raw1 := raw1) (hist0 := hist0) (hist1 := hist1)
    (matrixPtr := matrixPtr) (work := work) (scheduleMaps := scheduleMaps)
    hw (by omega) hspace (by omega) hbits hmaps hraw0 hraw1 hhist0 hhist1 hmatrix hschedule houtSpace
    hhostWord hmaskRead₂ hbitsRead
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
      | refine Light.Ends.callToThen (hh _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hh ?_ ?_ ?_ ?_);
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
        ((rintro vh μ₃ ⟨hvh, hdata, hrows, hselection, hkeep₃⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  refine ⟨hvh,hdata,hrows,hselection,?_⟩
  intro a ha
  change μ₃ a = μ a
  rw [hkeep₃ a (by omega),hkeep₂ a ⟨by omega,Or.inl (by omega)⟩]
  exact hkeep₁ a ⟨by omega,Or.inl ha⟩





















end ThreeSum.LightLocalCoverBuild

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (S : ThreeSum.LightLocalCoverBuild.Procs P pMain)
  {μ : Nat → Int} {h masks bitPtr maps raw0 raw1 hist0 hist1 matrixPtr work scheduleMaps : Nat},
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
          (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
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
            bitPtr →
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
                                (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightLocalCoverBuild.word h)) lim.word →
                              Light.Meets lim P pMain d
                                (@List.cons.{0} Int
                                  (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                                    (@OfNat.ofNat.{0} Int (nat_lit 512) (@instOfNat (nat_lit 512)))
                                    (@Nat.cast.{0} Int instNatCastInt h))
                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt h)
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
                                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                                              (@List.cons.{0} Int
                                                                (@Nat.cast.{0} Int instNatCastInt
                                                                  (ThreeSum.GlobalEncoding.scheduleSize h))
                                                                (@List.cons.{0} Int
                                                                  (@Nat.cast.{0} Int instNatCastInt scheduleMaps)
                                                                  (@List.nil.{0} Int))))))))))))))))))
                                μ (ThreeSum.LightLocalCoverBuild.time h) fun (r : Int) (ν : Nat → Int) =>
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
                                        (Light.Kept μ ν masks)))) := by
  exact @ThreeSum.LightLocalCoverBuild.Procs.meets_sourceProof

#print axioms solution
