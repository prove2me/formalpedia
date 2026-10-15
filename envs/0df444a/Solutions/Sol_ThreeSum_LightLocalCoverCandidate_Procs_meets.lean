-- Prove2me | solution 1 for ThreeSum.LightLocalCoverCandidate.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:28:32.61847+00:00
-- url     : https://prove2.me/submissions/6fe57978-a952-4917-84e8-8c6a60914e78

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
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
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
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
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
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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
import Theorems.Thm_ThreeSum_LightLocalCoverHashHistogram_meets
import Theorems.Thm_ThreeSum_LightLocalCoverRow_Procs_meets
import Theorems.Thm_ThreeSum_LightWeightDecode_Procs_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments

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
# A linear-time histogram procedure in the benchmark language

The input is an array of already computed residue indices in `[0,p)`.
The output is cleared and incremented once per input item. Multiplicities
are retained, including repeated equal residues.
-/

namespace ThreeSum.LightHistogram

open Light Finset

variable {lim : Limits} {P : Program} {d : ℕ}







theorem count_le (key : ℕ → ℕ) (r i : ℕ) : count key r i ≤ i := by
  exact (Finset.card_filter_le _ _).trans (by simp)






































































































end ThreeSum.LightHistogram

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


























































































































































theorem digit_lt {p width k coordinate : ℕ} (hp : 0 < p) : digit p width k coordinate < p :=
  Nat.mod_lt _ hp



































end ThreeSum.WeightEnumeration

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
# One complete local candidate: coefficients, bucket counts, and cover row

All data are constructed by fixed benchmark-language procedures. Separate
candidate histograms and coefficient rows are retained, while raw hash and
residue buffers are reusable. The preservation contract supports the outer
exhaustive candidate loop without forgetting previously completed rows.
-/

namespace ThreeSum.LightLocalCoverCandidate

open Light

set_option maxHeartbeats 2000000
set_option maxRecDepth 6000



































variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets_sourceProof {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {L n p cap index masks bitPtr coef raw0 raw1 hist0 hist1 dst work : ℕ}
    (mask w0 w1 : ℕ → ℕ) (bits : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+4 ≤ lim.depth) (hp : 0 < p) (hn : 0 < n)
    (hspace : space work L n p ≤ lim.space)
    (hmasks : masks+n ≤ coef) (hbits : bitPtr+n*L ≤ coef) (hcoef : coef+2*L ≤ raw0)
    (hraw0 : raw0+2*n ≤ raw1) (hraw1 : raw1+2*n ≤ hist0)
    (hhist0 : hist0+p ≤ hist1) (hhist1 : hist1+p ≤ dst) (hdst : dst+p*p ≤ work)
    (hword : (word L n p cap index : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^L)
    (hbitsRead : ∀ i < n, ∀ j < L, μ (bitPtr+i*L+j) = (bits i j : ℤ))
    (hbitsValue : ∀ i < n, ∀ j < L, bits i j ≤ 1)
    (hw0 : ∀ i < L, w0 i = WeightEnumeration.digit p (2*L) index (2*i))
    (hw1 : ∀ i < L, w1 i = WeightEnumeration.digit p (2*L) index (2*i+1)) :
    Meets lim P pMain d [L,p,index,n,cap,masks,bitPtr,coef,raw0,raw1,hist0,hist1,dst,work] μ
      (time L n p index)
      (fun _ μ' => LightWeightDecode.Rows μ' coef L p index ∧
        (∀ r < p,
          μ' (hist0+r) = (LightHistogram.count (LightHashHistogram.code L p mask w0 w1) r n : ℤ) ∧
          μ' (hist1+r) = (LightHistogram.count (LightHashHistogram.code L p mask w1 w0) r n : ℤ)) ∧
        (∀ r < p*p, μ' (dst+r) = (entry L n p cap mask bits w0 w1 r : ℤ)) ∧
        Preserved μ μ' work coef raw0 raw1 hist0 hist1 dst L n p) := by
  have hwork : work ≤ lim.space := by unfold space at hspace; omega
  have hdecodeSpace : work+(2*L+1) ≤ lim.space := by unfold space at hspace; omega
  have hhashSpace : LightHashHistogram.space work L p ≤ lim.space := by
    unfold space at hspace
    unfold LightHashHistogram.space
    omega
  have hrowSpace : work+2*(n*n) ≤ lim.space := by unfold space at hspace; omega
  have hbudget (x : ℕ) (hx : x ≤ word L n p cap index) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hdecodeWord := hbudget (LightWeightDecode.word L p index) (by unfold word; omega)
  have hhashWord := hbudget (LightHashHistogram.word L p p) (by unfold word; omega)
  have hrowWord := hbudget (LightPairFlags.word L n p cap) (by unfold word; omega)
  have hindexWord := hbudget index (by unfold word LightWeightDecode.word LightWeightRow.word; omega)
  have hnWord := hbudget n (by unfold word LightPairFlags.word; omega)
  have hLWord := hbudget L (by unfold word LightPairFlags.word; omega)
  have hpWord := hbudget p (by unfold word LightPairFlags.word; omega)
  have hcapWord := hbudget cap (by unfold word LightPairFlags.word; omega)
  have hb0 : ∀ i < L, w0 i ≤ p := by
    intro i hi
    rw [hw0 i hi]
    exact Nat.le_of_lt (WeightEnumeration.digit_lt hp)
  have hb1 : ∀ i < L, w1 i ≤ p := by
    intro i hi
    rw [hw1 i hi]
    exact Nat.le_of_lt (WeightEnumeration.digit_lt hp)
  apply Meets.of_body S.main
  unfold body time
  have hdcall := S.decode.meets (d := d+1) (μ := μ) (L := L) (p := p) (k := index)
    (dst := coef) (work := work) hw (by omega) (by omega) (by omega) hdecodeSpace hdecodeWord
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
      | refine Light.Ends.callToThen (hdcall _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hdcall ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightWeightDecode.time, LightWeightRow.time, LightRadixDigit.time,
                LightHashHistogram.time, LightLocalCoverRow.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightWeightDecode.time, LightWeightRow.time,
                LightRadixDigit.time, LightHashHistogram.time,
                LightLocalCoverRow.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, LightWeightDecode.time,
                LightWeightRow.time, LightRadixDigit.time,
                LightHashHistogram.time, LightLocalCoverRow.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro value₀ μ₁ ⟨hrows, _, hkeep₀⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hmask₁ : ∀ i < n, μ₁ (masks+i) = (mask i : ℤ) := by
    intro i hi
    rw [hkeep₀ _ ⟨by omega,Or.inl (by omega)⟩]
    exact hmaskRead i hi
  have hc0 : ∀ i < L, μ₁ (coef+i) = (w0 i : ℤ) := by
    intro i hi
    rw [(hrows i hi).1,hw0 i hi]
  have hc1 : ∀ i < L, μ₁ (coef+L+i) = (w1 i : ℤ) := by
    intro i hi
    rw [(hrows i hi).2,hw1 i hi]
  have hlcall := LightLocalCoverHashHistogram.meets S.hash (d := d+1) (μ := μ₁)
    (L := L) (n := n) (p := p) (U := p) (masks := masks) (raw := raw0) (codes := raw0+n)
    (hist := hist0) (src0 := coef) (src1 := coef+L) (work := work) mask w0 w1
    hw (by omega) hp hhashSpace (by omega) (by omega) (by omega) le_rfl (by omega) (by omega)
    hhashWord hmask₁ hmaskLt hc0 hc1 hb0 hb1
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
      | refine Light.Ends.callToThen (hlcall _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hlcall ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightWeightDecode.time, LightWeightRow.time, LightRadixDigit.time,
                LightHashHistogram.time, LightLocalCoverRow.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightWeightDecode.time, LightWeightRow.time,
                LightRadixDigit.time, LightHashHistogram.time,
                LightLocalCoverRow.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, LightWeightDecode.time,
                LightWeightRow.time, LightRadixDigit.time,
                LightHashHistogram.time, LightLocalCoverRow.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro value₁ μ₂ ⟨hleftCodes, hleftCounts, hkeep₁, hpres₁⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hmask₂ : ∀ i < n, μ₂ (masks+i) = (mask i : ℤ) := by
    intro i hi
    rw [hkeep₁ _ (by omega)]
    exact hmask₁ i hi
  have hc0₂ : ∀ i < L, μ₂ (coef+i) = (w0 i : ℤ) := by
    intro i hi
    rw [hkeep₁ _ (by omega)]
    exact hc0 i hi
  have hc1₂ : ∀ i < L, μ₂ (coef+L+i) = (w1 i : ℤ) := by
    intro i hi
    rw [hkeep₁ _ (by omega)]
    exact hc1 i hi
  have hrcall := LightLocalCoverHashHistogram.meets S.hash (d := d+1) (μ := μ₂)
    (L := L) (n := n) (p := p) (U := p) (masks := masks) (raw := raw1) (codes := raw1+n)
    (hist := hist1) (src0 := coef+L) (src1 := coef) (work := work) mask w1 w0
    hw (by omega) hp hhashSpace (by omega) (by omega) (by omega) le_rfl (by omega) (by omega)
    hhashWord hmask₂ hmaskLt hc1₂ hc0₂ hb1 hb0
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
      | refine Light.Ends.callToThen (hrcall _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hrcall ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightWeightDecode.time, LightWeightRow.time, LightRadixDigit.time,
                LightHashHistogram.time, LightLocalCoverRow.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightWeightDecode.time, LightWeightRow.time,
                LightRadixDigit.time, LightHashHistogram.time,
                LightLocalCoverRow.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, LightWeightDecode.time,
                LightWeightRow.time, LightRadixDigit.time,
                LightHashHistogram.time, LightLocalCoverRow.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro value₂ μ₃ ⟨hrightCodes, hrightCounts, hkeep₂, hpres₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hleftCodes₃ : ∀ i < n, μ₃ (raw0+n+i) = (LightHashHistogram.code L p mask w0 w1 i : ℤ) := by
    intro i hi
    rw [hkeep₂ _ (by omega)]
    exact hleftCodes i hi
  have hleftCounts₃ : ∀ r < p,
      μ₃ (hist0+r) = (LightHistogram.count (LightHashHistogram.code L p mask w0 w1) r n : ℤ) := by
    intro r hr
    rw [hpres₂ _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))]
    exact hleftCounts r hr
  have hbits₃ : ∀ i < n, ∀ j < L, μ₃ (bitPtr+i*L+j) = (bits i j : ℤ) := by
    intro i hi j hj
    have hm := Nat.mul_le_mul_right L (show i+1 ≤ n by omega)
    have ha : bitPtr+i*L+j < coef := by nlinarith
    rw [hkeep₂ _ (by omega),hkeep₁ _ (by omega),hkeep₀ _ ⟨by omega,Or.inl ha⟩]
    exact hbitsRead i hi j hj
  have hrowcall := S.row.meets (d := d+1) (μ := μ₃) (bitPtr := bitPtr)
    (leftPtr := raw0+n) (rightPtr := raw1+n) (leftHist := hist0) (rightHist := hist1)
    (dst := dst) (n := n) (L := L) (p := p) (cap := cap) (keys := work)
    bits (LightHashHistogram.code L p mask w0 w1) (LightHashHistogram.code L p mask w1 w0)
    (fun r => LightHistogram.count (LightHashHistogram.code L p mask w0 w1) r n)
    (fun r => LightHistogram.count (LightHashHistogram.code L p mask w1 w0) r n)
    hw (by omega) hn hp (by omega) (by omega) (by omega) (by omega) (by omega) hdst hrowSpace hrowWord
    hbits₃ hbitsValue hleftCodes₃ hrightCodes
    (fun _ _ => LightResidues.residue_lt hp 1 _) (fun _ _ => LightResidues.residue_lt hp 1 _)
    hleftCounts₃ hrightCounts (fun r _ => LightHistogram.count_le _ r n)
    (fun r _ => LightHistogram.count_le _ r n)
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
      | refine Light.Ends.callToThen (hrowcall _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hrowcall ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightWeightDecode.time, LightWeightRow.time, LightRadixDigit.time,
                LightHashHistogram.time, LightLocalCoverRow.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightWeightDecode.time, LightWeightRow.time,
                LightRadixDigit.time, LightHashHistogram.time,
                LightLocalCoverRow.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, LightWeightDecode.time,
                LightWeightRow.time, LightRadixDigit.time,
                LightHashHistogram.time, LightLocalCoverRow.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro value₃ μ₄ ⟨hout, hkeep₃⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  refine ⟨?_,?_,hout,?_⟩
  · intro i hi
    constructor
    · change μ₄ (coef+i) = _
      rw [hkeep₃ _ ⟨by omega,Or.inl (by omega)⟩,hkeep₂ _ (by omega),hkeep₁ _ (by omega)]
      exact (hrows i hi).1
    · change μ₄ (coef+L+i) = _
      rw [hkeep₃ _ ⟨by omega,Or.inl (by omega)⟩,hkeep₂ _ (by omega),hkeep₁ _ (by omega)]
      exact (hrows i hi).2
  · intro r hr
    constructor
    · change μ₄ (hist0+r) = _
      rw [hkeep₃ _ ⟨by omega,Or.inl (by omega)⟩]
      exact hleftCounts₃ r hr
    · change μ₄ (hist1+r) = _
      rw [hkeep₃ _ ⟨by omega,Or.inl (by omega)⟩]
      exact hrightCounts r hr
  · intro a ha hc hr0 hr1 hh0 hh1 hd
    change μ₄ a = μ a
    rw [hkeep₃ a ⟨ha,hd⟩,hpres₂ a ha (by omega) (by omega) hh1,
      hpres₁ a ha (by omega) (by omega) hh0]
    exact hkeep₀ a ⟨ha,hc⟩













end ThreeSum.LightLocalCoverCandidate

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (S : ThreeSum.LightLocalCoverCandidate.Procs P pMain)
  {μ : Nat → Int} {L n p cap index masks bitPtr coef raw0 raw1 hist0 hist1 dst work : Nat} (mask w0 w1 : Nat → Nat)
  (bits : Nat → Nat → Nat),
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d L)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        lim.depth →
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p →
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
          @LE.le.{0} Nat instLENat (ThreeSum.LightLocalCoverCandidate.space work L n p) lim.space →
            @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) masks n) coef →
              @LE.le.{0} Nat instLENat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bitPtr
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n L))
                  coef →
                @LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) coef
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L))
                    raw0 →
                  @LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) raw0
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
                      raw1 →
                    @LE.le.{0} Nat instLENat
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) raw1
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
                        hist0 →
                      @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) hist0 p)
                          hist1 →
                        @LE.le.{0} Nat instLENat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) hist1 p) dst →
                          @LE.le.{0} Nat instLENat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p p))
                              work →
                            @LE.le.{0} Int Int.instLEInt
                                (@Nat.cast.{0} Int instNatCastInt
                                  (ThreeSum.LightLocalCoverCandidate.word L n p cap index))
                                lim.word →
                              (∀ (i : Nat),
                                  @LT.lt.{0} Nat instLTNat i n →
                                    @Eq.{1} Int
                                      (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) masks i))
                                      (@Nat.cast.{0} Int instNatCastInt (mask i))) →
                                (∀ (i : Nat),
                                    @LT.lt.{0} Nat instLTNat i n →
                                      @LT.lt.{0} Nat instLTNat (mask i)
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)) →
                                  (∀ (i : Nat),
                                      @LT.lt.{0} Nat instLTNat i n →
                                        ∀ (j : Nat),
                                          @LT.lt.{0} Nat instLTNat j L →
                                            @Eq.{1} Int
                                              (μ
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    bitPtr
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i
                                                      L))
                                                  j))
                                              (@Nat.cast.{0} Int instNatCastInt (bits i j))) →
                                    (∀ (i : Nat),
                                        @LT.lt.{0} Nat instLTNat i n →
                                          ∀ (j : Nat),
                                            @LT.lt.{0} Nat instLTNat j L →
                                              @LE.le.{0} Nat instLENat (bits i j)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                      (∀ (i : Nat),
                                          @LT.lt.{0} Nat instLTNat i L →
                                            @Eq.{1} Nat (w0 i)
                                              (ThreeSum.WeightEnumeration.digit p
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)
                                                index
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i))) →
                                        (∀ (i : Nat),
                                            @LT.lt.{0} Nat instLTNat i L →
                                              @Eq.{1} Nat (w1 i)
                                                (ThreeSum.WeightEnumeration.digit p
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)
                                                  index
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
                                          Light.Meets lim P pMain d
                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt p)
                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt index)
                                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
                                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cap)
                                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt masks)
                                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt bitPtr)
                                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt coef)
                                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt raw0)
                                                              (@List.cons.{0} Int
                                                                (@Nat.cast.{0} Int instNatCastInt raw1)
                                                                (@List.cons.{0} Int
                                                                  (@Nat.cast.{0} Int instNatCastInt hist0)
                                                                  (@List.cons.{0} Int
                                                                    (@Nat.cast.{0} Int instNatCastInt hist1)
                                                                    (@List.cons.{0} Int
                                                                      (@Nat.cast.{0} Int instNatCastInt dst)
                                                                      (@List.cons.{0} Int
                                                                        (@Nat.cast.{0} Int instNatCastInt work)
                                                                        (@List.nil.{0} Int)))))))))))))))
                                            μ (ThreeSum.LightLocalCoverCandidate.time L n p index)
                                            fun (x : Int) (μ' : Nat → Int) =>
                                            And (ThreeSum.LightWeightDecode.Rows μ' coef L p index)
                                              (And
                                                (∀ (r : Nat),
                                                  @LT.lt.{0} Nat instLTNat r p →
                                                    And
                                                      (@Eq.{1} Int
                                                        (μ'
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) hist0 r))
                                                        (@Nat.cast.{0} Int instNatCastInt
                                                          (ThreeSum.LightHistogram.count
                                                            (ThreeSum.LightHashHistogram.code L p mask w0 w1) r n)))
                                                      (@Eq.{1} Int
                                                        (μ'
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) hist1 r))
                                                        (@Nat.cast.{0} Int instNatCastInt
                                                          (ThreeSum.LightHistogram.count
                                                            (ThreeSum.LightHashHistogram.code L p mask w1 w0) r n))))
                                                (And
                                                  (∀ (r : Nat),
                                                    @LT.lt.{0} Nat instLTNat r
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          p p) →
                                                      @Eq.{1} Int
                                                        (μ'
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) dst r))
                                                        (@Nat.cast.{0} Int instNatCastInt
                                                          (ThreeSum.LightLocalCoverCandidate.entry L n p cap mask bits
                                                            w0 w1 r)))
                                                  (ThreeSum.LightLocalCoverCandidate.Preserved μ μ' work coef raw0 raw1
                                                    hist0 hist1 dst L n p))) := by
  exact @ThreeSum.LightLocalCoverCandidate.Procs.meets_sourceProof

#print axioms solution
