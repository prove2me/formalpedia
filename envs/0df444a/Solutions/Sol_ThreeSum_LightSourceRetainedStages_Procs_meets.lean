-- Prove2me | solution 1 for ThreeSum.LightSourceRetainedStages.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:45:43.854349+00:00
-- url     : https://prove2.me/submissions/dfcafd9f-b1cb-4882-a4a7-998981d0595c

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
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
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
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
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
import Theorems.Thm_ThreeSum_LightSourceGather_meets
import Theorems.Thm_ThreeSum_LightZetaStages_meets
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
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







































































































end ThreeSum.LightResidues

end

section


/-!
# Compact addresses for bounded-cardinality bit masks

Both ranking and enumeration recurse on the highest available bit. The
enumerator stops immediately when the requested layer is empty. In
particular, it does not enumerate the ambient Boolean cube and filter it.
-/

namespace ThreeSum.SubsetAddress

set_option maxRecDepth 4000

open Finset
open scoped BigOperators






































































































































































































































@[simp] theorem layerOffset_zero (L : ℕ) : layerOffset L 0 = 0 := by
  simp [layerOffset]

theorem layerOffset_succ (L k : ℕ) :
    layerOffset L (k + 1) = layerOffset L k + L.choose k := by
  exact Finset.sum_range_succ _ _

theorem layerOffset_mono (L : ℕ) : Monotone (layerOffset L) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [layerOffset_succ]
  omega






theorem downsetRank_lt {L cut m : ℕ} (hm : m < 2 ^ L) (hk : weight L m ≤ cut) :
    downsetRank L m < downsetCap L cut := by
  have hmask : IsMask L (weight L m) m := ⟨hm, rfl⟩
  have hr := layerRank_lt hmask
  unfold downsetRank downsetCap
  calc
    _ < layerOffset L (weight L m) + L.choose (weight L m) := Nat.add_lt_add_left hr _
    _ = layerOffset L (weight L m + 1) := (layerOffset_succ L _).symm
    _ ≤ _ := layerOffset_mono L (Nat.succ_le_succ (le_min hk hmask.le_width))






























theorem enumerateThrough_length (L k : ℕ) :
    (enumerateThrough L k).length = layerOffset L (k + 1) := by
  induction k with
  | zero => simp [enumerateThrough, enumerateLayer_length, layerOffset_succ]
  | succ k ih =>
      rw [enumerateThrough, List.length_append, ih, enumerateLayer_length,
        layerOffset_succ L (k + 1)]

theorem enumerateDownset_length (L cut : ℕ) :
    (enumerateDownset L cut).length = downsetCap L cut :=
  enumerateThrough_length L (min cut L)

theorem mem_enumerateThrough (L k m : ℕ) :
    m ∈ enumerateThrough L k ↔ m < 2 ^ L ∧ weight L m ≤ k := by
  induction k with
  | zero => simp [enumerateThrough, mem_enumerateLayer, IsMask]
  | succ k ih =>
      simp only [enumerateThrough, List.mem_append, ih, mem_enumerateLayer, IsMask]
      omega

theorem mem_enumerateDownset (L cut m : ℕ) :
    m ∈ enumerateDownset L cut ↔ m < 2 ^ L ∧ weight L m ≤ cut := by
  rw [enumerateDownset, mem_enumerateThrough]
  constructor
  · rintro ⟨hm, hk⟩
    exact ⟨hm, hk.trans (min_le_left _ _)⟩
  · rintro ⟨hm, hk⟩
    exact ⟨hm, le_min hk (weight_le_width hm)⟩































































































theorem subsetRank_lt {L cut : ℕ} {s : Finset (Fin L)} (hs : s.card ≤ cut) :
    subsetRank s < downsetCap L cut := by
  have hm := subsetMask_isMask s
  exact downsetRank_lt hm.1 (hm.2.trans_le hs)







































end ThreeSum.SubsetAddress

end

section


/-!
# The actual compact enumeration uses the actual compact table addresses

This bridges a sequentially constructed source array to `TableAt`: the mask
stored at `subsetRank S` by the existing enumerator is exactly `subsetMask S`.
No additional scatter, rank oracle, or arbitrary enumeration is required.
-/

namespace ThreeSum.SourceTableLayout

open SubsetAddress

set_option maxHeartbeats 800000

theorem layerRank_zero (L : ℕ) : layerRank L 0 0 = 0 := by
  induction L with
  | zero => rfl
  | succ L ih => simpa only [layerRank,if_pos (Nat.two_pow_pos L)] using ih

theorem getD_map_of_lt {α β : Type*} (l : List α) (f : α → β)
    (a : α) (b : β) {i : ℕ} (hi : i < l.length) :
    (l.map f).getD i b = f (l.getD i a) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getD_eq_getElem _ _ hi]
  exact List.getElem_map ..

theorem enumerateLayer_getD_rank {L k m : ℕ} (hm : IsMask L k m) (fallback : ℕ) :
    (enumerateLayer L k).getD (layerRank L k m) fallback = m := by
  induction L generalizing k m fallback with
  | zero =>
      have hk := hm.le_width
      have hb := hm.1
      have hk0 : k=0 := by omega
      have hm0 : m=0 := by simp only [pow_zero] at hb; omega
      subst k; subst m
      simp [enumerateLayer,layerRank]
  | succ L ih =>
      cases k with
      | zero =>
          have hm0 := (isMask_zero (L+1) m).mp hm
          subst m
          simp [enumerateLayer,layerRank_zero]
      | succ k =>
          rw [enumerateLayer,if_pos hm.le_width]
          by_cases hc : m < 2^L
          · rw [layerRank,if_pos hc]
            rw [List.getD_append _ _ _ _ (by
              rw [enumerateLayer_length]
              exact layerRank_lt (hm.low hc))]
            exact ih (hm.low hc) fallback
          · have hh := (hm.high (Nat.le_of_not_gt hc)).2
            simp only [Nat.add_sub_cancel] at hh
            rw [layerRank,if_neg hc]
            simp only [Nat.add_sub_cancel]
            rw [List.getD_append_right _ _ _ _ (by
              rw [enumerateLayer_length]
              omega),enumerateLayer_length,Nat.add_sub_cancel_left]
            rw [getD_map_of_lt _ _ 0 _ (by
              rw [enumerateLayer_length]
              exact layerRank_lt hh),ih hh 0]
            omega

theorem enumerateThrough_getD_rank {L k m cut : ℕ} (hm : IsMask L k m)
    (hk : k ≤ cut) (fallback : ℕ) :
    (enumerateThrough L cut).getD (downsetRank L m) fallback = m := by
  induction cut with
  | zero =>
      have hk0 : k=0 := by omega
      subst k
      simpa only [enumerateThrough,downsetRank,hm.2,layerOffset_zero,zero_add] using
        enumerateLayer_getD_rank hm fallback
  | succ cut ih =>
      rw [enumerateThrough]
      by_cases hlow : k ≤ cut
      · rw [List.getD_append _ _ _ _ (by
          rw [enumerateThrough_length]
          have hlt := layerRank_lt hm
          have hle := layerOffset_mono L (Nat.succ_le_succ hlow)
          simp only [Nat.succ_eq_add_one] at hle
          rw [layerOffset_succ L k] at hle
          unfold downsetRank
          rw [hm.2]
          omega)]
        exact ih hlow
      · have he : k=cut+1 := by omega
        subst k
        rw [downsetRank,hm.2]
        rw [List.getD_append_right _ _ _ _ (by
          rw [enumerateThrough_length]
          omega),enumerateThrough_length,Nat.add_sub_cancel_left]
        exact enumerateLayer_getD_rank hm fallback

theorem enumerateDownset_getD_rank {L cut m : ℕ}
    (hm : m < 2^L) (hk : weight L m ≤ cut) (fallback : ℕ) :
    (enumerateDownset L cut).getD (downsetRank L m) fallback = m := by
  exact enumerateThrough_getD_rank ⟨hm,rfl⟩ (le_min hk (weight_le_width hm)) fallback

theorem enumerateDownset_getD_subsetRank {L cut : ℕ} (S : Finset (Fin L))
    (hS : S.card ≤ cut) (fallback : ℕ) :
    (enumerateDownset L cut).getD (subsetRank S) fallback = subsetMask S := by
  have hmask := subsetMask_isMask S
  exact enumerateDownset_getD_rank hmask.1 (hmask.2.trans_le hS) fallback





theorem maskAt_mem {L cut i : ℕ} (hi : i < downsetCap L cut) :
    maskAt L cut i ∈ enumerateDownset L cut := by
  unfold maskAt
  rw [List.getD_eq_getElem _ _ (by simpa only [enumerateDownset_length] using hi)]
  exact List.getElem_mem _

theorem maskAt_lt {L cut i : ℕ} (hi : i < downsetCap L cut) :
    maskAt L cut i < 2^L :=
  ((mem_enumerateDownset L cut _).mp (maskAt_mem hi)).1

theorem setAt_card {L cut i : ℕ} (hi : i < downsetCap L cut) :
    (setAt L cut i).card ≤ cut := by
  rw [setAt,MaskDecode.decode_card (maskAt_lt hi)]
  exact ((mem_enumerateDownset L cut _).mp (maskAt_mem hi)).2





theorem setAt_subsetRank {L cut : ℕ} (S : Finset (Fin L)) (hS : S.card ≤ cut) :
    setAt L cut (subsetRank S) = S := by
  rw [setAt,maskAt,enumerateDownset_getD_subsetRank S hS,MaskDecode.decode_subsetMask]













theorem tableAt_of_setAt {L cut base : ℕ} {μ : ℕ → ℤ}
    (f : Finset (Fin L) → ℤ)
    (hread : ∀ i < downsetCap L cut, μ (base+i) = f (setAt L cut i)) :
    LightZetaCell.TableAt μ base cut f := by
  intro S hS
  rw [hread _ (subsetRank_lt hS),setAt_subsetRank S hS]

end ThreeSum.SourceTableLayout

end

section


/-!
# Original-input histogram construction followed by all suffix zeta stages

This fixed program constructs a trimmed source table from the physical input
array, then feeds that exact table into the existing costed suffix transform.
The rank/enumeration proof connects the sequential source writes to the
compact addresses. No initially populated source or zeta table is assumed.
-/

namespace ThreeSum.LightSourceStages

open Light SubsetAddress LightSubsetAddress LightPascal LightZetaCell

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000






























variable {lim : Limits} {P : Program} {d : ℕ}

theorem ZetaProcs.meets {pMain : ℕ} (C : ZetaProcs P pMain)
    {μ : ℕ → ℤ} {L cut base maskBase work U : ℕ} (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hdata : base+(L+1)*downsetCap L cut ≤ maskBase)
    (hmasks : maskBase+downsetCap L cut ≤ work)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^L*U : ℕ) : ℤ) ≤ lim.word)
    (hread : TableAt μ base cut f) (hvalues : ∀ T, T.card ≤ cut → |f T| ≤ U)
    (hd : d+L+7 ≤ lim.depth) :
    Meets lim P pMain d [L,cut,base,maskBase,work] μ (LightZetaStages.time L cut)
      (fun _ ν => LightZetaStages.StoredThrough ν base cut f L ∧
        KeptBut μ ν maskBase base ((L+1)*downsetCap L cut)) :=
  LightZetaStages.meets C.main C.size C.pass C.enumSetup C.enumeration C.batch C.cell
    C.setup C.offset C.erase f hw hcut hdata hmasks hspace hword hvalueWord hread hvalues hd

































































































































end ThreeSum.LightSourceStages

end

section


/-!
# Source stages gathered from a retained original-input histogram

The histogram is built once for a source band and fixed modulus/offset by
`LightSourceHistogram`. This program then gathers the independently trimmed
source for each occurrence vector and runs the actual suffix transforms.
Neither the original array nor the full histogram is rescanned in this loop.
-/

namespace ThreeSum.LightSourceRetainedStages

open Light SubsetAddress LightSubsetAddress LightPascal LightZetaCell

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000





theorem source_abs_le {L m B : ℕ} (hm : 0 < m)
    (endpoint : Finset (Fin L) → ℤ) (flag : Finset (Fin L) → ℕ) (hist : ℕ → ℕ)
    (hhist : ∀ r < m, hist r ≤ B) (S : Finset (Fin L)) :
    |source m endpoint flag hist S| ≤ (B : ℤ) := by
  unfold source
  rw [Int.abs_natCast]
  apply Int.ofNat_le.mpr
  split
  · exact hhist _ (LightResidues.residue_lt hm 1 _)
  · omega

























variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets_sourceProof {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {raw flags table base m work L cut maskBase E B : ℕ}
    (endpoint : Finset (Fin L) → ℤ) (flag : Finset (Fin L) → ℕ) (hist : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+8 ≤ lim.depth)
    (hm : 0 < m) (hcut : cut ≤ L)
    (hraw : raw+downsetCap L cut ≤ base) (hflags : flags+downsetCap L cut ≤ base)
    (htable : table+m ≤ base) (hdata : base+(L+1)*downsetCap L cut ≤ maskBase)
    (hmasks : maskBase+downsetCap L cut ≤ work)
    (hspace : space work L E ≤ lim.space)
    (hword : (word L m E B : ℤ) ≤ lim.word)
    (hrawRead : ∀ i < downsetCap L cut,
      μ (raw+i) = endpoint (SourceTableLayout.setAt L cut i))
    (hrawBound : ∀ S, S.card ≤ cut → |endpoint S| ≤ (E : ℤ))
    (hflagRead : ∀ i < downsetCap L cut,
      μ (flags+i) = (flag (SourceTableLayout.setAt L cut i) : ℤ))
    (hflagBound : ∀ S, S.card ≤ cut → flag S ≤ 1)
    (hhistRead : ∀ r < m, μ (table+r) = (hist r : ℤ))
    (hhistBound : ∀ r < m, hist r ≤ B) :
    Meets lim P pMain d [raw,flags,table,base,m,work,L,cut,maskBase,downsetCap L cut]
      μ (time L cut E) (fun _ ν =>
        LightZetaStages.StoredThrough ν base cut (source m endpoint flag hist) L ∧
        Kept μ ν base) := by
  have hsGather : work+(Nat.log 2 (E+1)+2) ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hsZeta : work+tableSize L+(L+1) ≤ lim.space :=
    (le_max_right _ _).trans hspace
  have hwGather : (4*E+4*m+16 : ℤ) ≤ lim.word := by
    have hh : 4*E+4*m+16 ≤ word L m E B := by unfold word; omega
    exact_mod_cast (Int.ofNat_le.mpr hh).trans hword
  have hwB : (B : ℤ) ≤ lim.word := by
    have hh : B ≤ word L m E B := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwZeta : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : (L+1)*2^(L+1) ≤ word L m E B := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwValues : ((2^L*B : ℕ) : ℤ) ≤ lim.word := by
    have hh : 2^L*B ≤ word L m E B := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hcap : downsetCap L cut ≤ (L+1)*downsetCap L cut :=
    Nat.le_mul_of_pos_left _ (by omega)
  apply Meets.of_body C.main
  unfold body time
  have hg := LightSourceGather.meets C.gather C.emod (d := d+1) (μ := μ)
    (raw := raw) (flags := flags) (table := table) (dst := base)
    (n := downsetCap L cut) (m := m) (work := work) (U := E) (B := B)
    (fun i => endpoint (SourceTableLayout.setAt L cut i))
    (fun i => flag (SourceTableLayout.setAt L cut i)) hist
    hw (by omega) hm hraw hflags htable (by omega) hsGather hwGather hwB
    hrawRead (fun i hi => hrawBound _ (SourceTableLayout.setAt_card hi))
    hflagRead (fun i hi => hflagBound _ (SourceTableLayout.setAt_card hi)) hhistRead hhistBound
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
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightSourceGather.time, LightZetaStages.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightSourceGather.time, LightZetaStages.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, LightSourceGather.time,
                LightZetaStages.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro r ν₁ ⟨out, kept₁⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have htableAt : TableAt ν₁ base cut (source m endpoint flag hist) := by
    apply SourceTableLayout.tableAt_of_setAt
    exact out
  have hz := C.zeta.meets (d := d+1) (μ := ν₁) (L := L) (cut := cut)
    (base := base) (maskBase := maskBase) (work := work) (U := B)
    (source m endpoint flag hist) hw hcut hdata hmasks hsZeta hwZeta hwValues htableAt
    (fun S _ => source_abs_le hm endpoint flag hist hhistBound S) (by omega)
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
      | refine Light.Ends.callToThen (hz _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hz ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightSourceGather.time, LightZetaStages.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightSourceGather.time, LightZetaStages.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, LightSourceGather.time,
                LightZetaStages.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro r ν₂ ⟨stored, kept₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  refine ⟨stored,?_⟩
  intro a ha
  exact (kept₂ a ⟨by omega,Or.inl (by omega)⟩).trans
    (kept₁ a ⟨by omega,Or.inl ha⟩)























end ThreeSum.LightSourceRetainedStages

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (C : ThreeSum.LightSourceRetainedStages.Procs P pMain)
  {μ : Nat → Int} {raw flags table base m work L cut maskBase E B : Nat} (endpoint : Finset.{0} (Fin L) → Int)
  (flag : Finset.{0} (Fin L) → Nat) (hist : Nat → Nat),
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d L)
          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
        lim.depth →
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
        @LE.le.{0} Nat instLENat cut L →
          @LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) raw
                (ThreeSum.SubsetAddress.downsetCap L cut))
              base →
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flags
                  (ThreeSum.SubsetAddress.downsetCap L cut))
                base →
              @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) table m) base →
                @LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) L
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (ThreeSum.SubsetAddress.downsetCap L cut)))
                    maskBase →
                  @LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maskBase
                        (ThreeSum.SubsetAddress.downsetCap L cut))
                      work →
                    @LE.le.{0} Nat instLENat (ThreeSum.LightSourceRetainedStages.space work L E) lim.space →
                      @LE.le.{0} Int Int.instLEInt
                          (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightSourceRetainedStages.word L m E B))
                          lim.word →
                        (∀ (i : Nat),
                            @LT.lt.{0} Nat instLTNat i (ThreeSum.SubsetAddress.downsetCap L cut) →
                              @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) raw i))
                                (endpoint (ThreeSum.SourceTableLayout.setAt L cut i))) →
                          (∀ (S : Finset.{0} (Fin L)),
                              @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin L) S) cut →
                                @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (endpoint S))
                                  (@Nat.cast.{0} Int instNatCastInt E)) →
                            (∀ (i : Nat),
                                @LT.lt.{0} Nat instLTNat i (ThreeSum.SubsetAddress.downsetCap L cut) →
                                  @Eq.{1} Int
                                    (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flags i))
                                    (@Nat.cast.{0} Int instNatCastInt
                                      (flag (ThreeSum.SourceTableLayout.setAt L cut i)))) →
                              (∀ (S : Finset.{0} (Fin L)),
                                  @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin L) S) cut →
                                    @LE.le.{0} Nat instLENat (flag S)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                (∀ (r : Nat),
                                    @LT.lt.{0} Nat instLTNat r m →
                                      @Eq.{1} Int
                                        (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) table r))
                                        (@Nat.cast.{0} Int instNatCastInt (hist r))) →
                                  (∀ (r : Nat), @LT.lt.{0} Nat instLTNat r m → @LE.le.{0} Nat instLENat (hist r) B) →
                                    Light.Meets lim P pMain d
                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt raw)
                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt flags)
                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt table)
                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt base)
                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt m)
                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
                                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cut)
                                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt maskBase)
                                                        (@List.cons.{0} Int
                                                          (@Nat.cast.{0} Int instNatCastInt
                                                            (ThreeSum.SubsetAddress.downsetCap L cut))
                                                          (@List.nil.{0} Int)))))))))))
                                      μ (ThreeSum.LightSourceRetainedStages.time L cut E)
                                      fun (x : Int) (ν : Nat → Int) =>
                                      And
                                        (@ThreeSum.LightZetaStages.StoredThrough L ν base cut
                                          (@ThreeSum.LightSourceRetainedStages.source L m endpoint flag hist) L)
                                        (Light.Kept μ ν base) := by
  exact @ThreeSum.LightSourceRetainedStages.Procs.meets_sourceProof

#print axioms solution
