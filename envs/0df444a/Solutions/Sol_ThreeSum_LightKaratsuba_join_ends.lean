-- Prove2me | solution 1 for ThreeSum.LightKaratsuba.join_ends
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:10:32.452984+00:00
-- url     : https://prove2.me/submissions/b5b6de8e-3cd8-4175-b5d7-2886d8472403

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
import Theorems.Thm_Light_Ends_pass
import Theorems.Thm_ThreeSum_LightArray_linear_bounded_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba

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
    ⟨seg_wrote List.length_replicate fun i hi => List.getElem_replicate .., by ((try refine Light.SameOn.cell ?_); (intro apspMacro_21661_0 apspMacro_21661_1);
                                                                                   (first
                                                                                     |
                                                                                       ((((repeat
                                                                                                 (((with_reducible
                                                                                                         rename Light.SameOn _ _ _ => apspMacro_21661_2));
                                                                                                   ((try
                                                                                                         have :=
                                                                                                           apspMacro_21661_2 apspMacro_21661_0 (by omega)));
                                                                                                   (revert apspMacro_21661_2)));
                                                                                             (intros);
                                                                                             (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                         (omega))
                                                                                     |
                                                                                       ((simp [] at apspMacro_21661_1);
                                                                                         (((repeat
                                                                                                 (((with_reducible
                                                                                                         rename Light.SameOn _ _ _ => apspMacro_21661_3));
                                                                                                   ((try
                                                                                                         have :=
                                                                                                           apspMacro_21661_3 apspMacro_21661_0 (by omega)));
                                                                                                   (revert apspMacro_21661_3)));
                                                                                             (intros);
                                                                                             (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                         (omega))
                                                                                     |
                                                                                       ((((repeat
                                                                                                 (((with_reducible
                                                                                                         rename Light.SameOn _ _ _ => apspMacro_21661_4));
                                                                                                   ((try
                                                                                                         have :=
                                                                                                           apspMacro_21661_4 apspMacro_21661_0 (by omega)));
                                                                                                   (revert apspMacro_21661_4)));
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
























































































theorem window_bound {f : ℕ → ℤ} {offset n j U : ℕ}
    (hf : ∀ i < n, |f i| ≤ U) : |window f offset n j| ≤ U := by
  unfold window
  split_ifs with hj
  · exact hf _ (by omega)
  · simpa using (Nat.cast_nonneg U : (0 : ℤ) ≤ U)

theorem linear_update_full {μ μ' : ℕ → ℤ} {out src offset n N : ℕ}
    {c : ℤ} {f g : ℕ → ℤ} (hfit : offset + n ≤ N)
    (hOld : ∀ j < N, μ (out + j) = f j)
    (hSrc : ∀ i < n, μ (src + i) = g i)
    (hWrite : ∀ i < n,
      μ' (out + offset + i) = μ (out + offset + i) + c * μ (src + i))
    (hkeep : SameOutside μ μ' (out + offset) n) :
    ∀ j < N, μ' (out + j) = f j + window (fun i => c * g i) offset n j := by
  intro j hj
  unfold window
  split_ifs with hin
  · have hi : j - offset < n := by omega
    have he : out + offset + (j - offset) = out + j := by omega
    have hr := hWrite (j - offset) hi
    rw [he, hOld j hj, hSrc _ hi] at hr
    exact hr
  · have hr := hkeep (out + j) (by omega)
    simpa only [add_zero, hOld j hj] using hr








section Join

variable {lim : Limits} {P : Program} {d pLinear pFill : ℕ}

theorem join_ends_sourceProof (hLinear : P[pLinear]? = some LightArray.linearBody)
    (hFill : P[pFill]? = some fillBody)
    {μ : ℕ → ℤ} {n half a b out work U : ℕ} {r : ℤ}
    (hn : 0 < n) (hhalf : 2 * half = n)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hout : out + 2 * n ≤ work) (hwork : work + 3 * n ≤ lim.space)
    (hword : 10 * (U : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (work + i)| ≤ U ∧ |μ (work + n + i)| ≤ U ∧
      |μ (work + 2 * n + i)| ≤ U)
    (hd : d < lim.depth) :
    Ends lim P d (joinBody pLinear pFill)
      ⟨frame [n, a, b, out, work, half, r], μ⟩ (joinTime n) fun σ' =>
      (∀ j < 2 * n, σ'.mem (out + j) = joined μ work n half j) ∧
        KeptBut μ σ'.mem work out (2 * n) := by
  unfold joinBody
  have hU : (0 : ℤ) ≤ U := Nat.cast_nonneg U
  have hcall1 := LightArray.linear_bounded_meets (d := d + 1) hLinear
    (μ := μ) (srcA := work + 2 * n) (srcB := work) (dst := work + 2 * n)
    (n := n) (U := U) (c := -1) hw (by omega) (by omega) (by omega)
    (Or.inl rfl) (Or.inr (by omega)) (by norm_num) (by omega)
    (fun i hi => ⟨(hvalues i hi).2.2, (hvalues i hi).1⟩)
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
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                joinTime, LightArray.linearTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [joinTime, LightArray.linearTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, joinTime,
                LightArray.linearTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro _ μ₁ ⟨hr₁, hk₁⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hz01 : ∀ i < n, μ₁ (work + i) = μ (work + i) :=
    fun i hi => hk₁ _ (by omega)
  have hz21 : ∀ i < n, μ₁ (work + n + i) = μ (work + n + i) :=
    fun i hi => hk₁ _ (by omega)
  have hm1 : ∀ i < n, |μ₁ (work + 2 * n + i)| ≤ 2 * (U : ℤ) := by
    intro i hi
    rw [hr₁ i hi]
    have hab := abs_sub (μ (work + 2 * n + i)) (μ (work + i))
    have hv := hvalues i hi
    simpa only [neg_one_mul, ← sub_eq_add_neg] using
      hab.trans (by omega : |μ (work + 2 * n + i)| + |μ (work + i)| ≤ 2 * (U : ℤ))
  have hcall2 := LightArray.linear_bounded_meets (d := d + 1) hLinear
    (μ := μ₁) (srcA := work + 2 * n) (srcB := work + n) (dst := work + 2 * n)
    (n := n) (U := 2 * U) (c := -1) hw (by omega) (by omega) (by omega)
    (Or.inl rfl) (Or.inr (by omega)) (by norm_num) (by push_cast; omega)
    (fun i hi => ⟨by simpa using hm1 i hi, by rw [hz21 i hi]; have := (hvalues i hi).2.1; push_cast; omega⟩)
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
      | refine Light.Ends.callToThen (hcall2 _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hcall2 ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                joinTime, LightArray.linearTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [joinTime, LightArray.linearTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, joinTime,
                LightArray.linearTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro _ μ₂ ⟨hr₂, hk₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hz02 : ∀ i < n, μ₂ (work + i) = μ (work + i) :=
    fun i hi => (hk₂ _ (by omega)).trans (hz01 i hi)
  have hz22 : ∀ i < n, μ₂ (work + n + i) = μ (work + n + i) :=
    fun i hi => (hk₂ _ (by omega)).trans (hz21 i hi)
  have hmiddle : ∀ i < n, μ₂ (work + 2 * n + i) =
      μ (work + 2 * n + i) - μ (work + i) - μ (work + n + i) := by
    intro i hi
    rw [hr₂ i hi, hr₁ i hi, hz21 i hi]
    ring
  have hm2 : ∀ i < n, |μ₂ (work + 2 * n + i)| ≤ 3 * (U : ℤ) := by
    intro i hi
    rw [hmiddle i hi]
    have h₁ := abs_sub (μ (work + 2 * n + i)) (μ (work + i))
    have h₂ := abs_sub (μ (work + 2 * n + i) - μ (work + i)) (μ (work + n + i))
    have hv := hvalues i hi
    omega
  have hfill := fill_meets (d := d + 1) hFill (μ := μ₂) (dst := out) (n := 2 * n)
    (x := 0) hw (by omega)
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
      | refine Light.Ends.callToThen (hfill _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hfill ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                joinTime, LightArray.linearTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [joinTime, LightArray.linearTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, joinTime,
                LightArray.linearTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro _ μ₃ ⟨hzeroSeg, hk₃⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hzero : ∀ j < 2 * n, μ₃ (out + j) = 0 := by
    intro j hj
    rw [hzeroSeg j (by simpa using hj)]
    exact List.getElem_replicate ..
  have hz03 : ∀ i < n, μ₃ (work + i) = μ (work + i) :=
    fun i hi => (hk₃ _ (by omega)).trans (hz02 i hi)
  have hz23 : ∀ i < n, μ₃ (work + n + i) = μ (work + n + i) :=
    fun i hi => (hk₃ _ (by omega)).trans (hz22 i hi)
  have hm3 : ∀ i < n, μ₃ (work + 2 * n + i) = μ₂ (work + 2 * n + i) :=
    fun i hi => hk₃ _ (by omega)
  have hcall3 := LightArray.linear_bounded_meets (d := d + 1) hLinear
    (μ := μ₃) (srcA := out) (srcB := work) (dst := out)
    (n := n) (U := U) (c := 1) hw (by omega) (by omega) (by omega)
    (Or.inl rfl) (Or.inr (by omega)) (by norm_num) (by omega)
    (fun i hi => ⟨by rw [hzero i (by omega), abs_zero]; exact hU,
      by rw [hz03 i hi]; exact (hvalues i hi).1⟩)
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
      | refine Light.Ends.callToThen (hcall3 _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hcall3 ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                joinTime, LightArray.linearTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [joinTime, LightArray.linearTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, joinTime,
                LightArray.linearTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro _ μ₄ ⟨hr₄, hk₄⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hfirst : ∀ j < 2 * n, μ₄ (out + j) = window (fun i => μ (work + i)) 0 n j := by
    have ht := linear_update_full (offset := 0) (by omega : 0 + n ≤ 2 * n)
      hzero hz03 (by simpa only [Nat.add_zero] using hr₄)
      (by simpa only [Nat.add_zero] using hk₄)
    simpa only [one_mul, zero_add] using ht
  have hz24 : ∀ i < n, μ₄ (work + n + i) = μ (work + n + i) :=
    fun i hi => (hk₄ _ (by omega)).trans (hz23 i hi)
  have hm4 : ∀ i < n, μ₄ (work + 2 * n + i) = μ₂ (work + 2 * n + i) :=
    fun i hi => (hk₄ _ (by omega)).trans (hm3 i hi)
  have hcall4 := LightArray.linear_bounded_meets (d := d + 1) hLinear
    (μ := μ₄) (srcA := out + half) (srcB := work + 2 * n) (dst := out + half)
    (n := n) (U := 3 * U) (c := 1) hw (by omega) (by omega) (by omega)
    (Or.inl rfl) (Or.inr (by omega)) (by norm_num) (by push_cast; omega)
    (fun i hi => ⟨by
      rw [show out + half + i = out + (half + i) by omega, hfirst _ (by omega)]
      have ht := window_bound (offset := 0) (j := half + i) (fun j hj => (hvalues j hj).1)
      push_cast; omega,
      by rw [hm4 i hi]; simpa using hm2 i hi⟩)
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
      | refine Light.Ends.callToThen (hcall4 _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hcall4 ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                joinTime, LightArray.linearTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [joinTime, LightArray.linearTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, joinTime,
                LightArray.linearTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro _ μ₅ ⟨hr₅, hk₅⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hm4' : ∀ i < n, μ₄ (work + 2 * n + i) =
      μ (work + 2 * n + i) - μ (work + i) - μ (work + n + i) :=
    fun i hi => (hm4 i hi).trans (hmiddle i hi)
  have hsecond : ∀ j < 2 * n, μ₅ (out + j) =
      window (fun i => μ (work + i)) 0 n j +
      window (fun i => μ (work + 2 * n + i) - μ (work + i) - μ (work + n + i)) half n j := by
    have ht := linear_update_full (by omega : half + n ≤ 2 * n) hfirst hm4' hr₅ hk₅
    simpa only [one_mul] using ht
  have hz25 : ∀ i < n, μ₅ (work + n + i) = μ (work + n + i) :=
    fun i hi => (hk₅ _ (by omega)).trans (hz24 i hi)
  have hcall5 := LightArray.linear_bounded_meets (d := d + 1) hLinear
    (μ := μ₅) (srcA := out + n) (srcB := work + n) (dst := out + n)
    (n := n) (U := 4 * U) (c := 1) hw (by omega) (by omega) (by omega)
    (Or.inl rfl) (Or.inr (by omega)) (by norm_num) (by push_cast; omega)
    (fun i hi => ⟨by
      rw [show out + n + i = out + (n + i) by omega, hsecond _ (by omega)]
      have h₁ := window_bound (offset := 0) (j := n + i) (fun j hj => (hvalues j hj).1)
      have h₂ : |window (fun j => μ (work + 2 * n + j) - μ (work + j) -
          μ (work + n + j)) half n (n + i)| ≤ 3 * (U : ℤ) := by
        have hv := window_bound (offset := half) (j := n + i) (U := 3 * U)
          (f := fun j => μ (work + 2 * n + j) - μ (work + j) - μ (work + n + j))
          (fun j hj => by rw [← hmiddle j hj]; simpa using hm2 j hj)
        simpa using hv
      have hs := abs_add_le
        (window (fun j => μ (work + j)) 0 n (n + i))
        (window (fun j => μ (work + 2 * n + j) - μ (work + j) - μ (work + n + j)) half n (n + i))
      push_cast; omega,
      by rw [hz25 i hi]; have := (hvalues i hi).2.1; push_cast; omega⟩)
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
      | refine Light.Ends.callToThen (hcall5 _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hcall5 ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                joinTime, LightArray.linearTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [joinTime, LightArray.linearTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, joinTime,
                LightArray.linearTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro _ μ₆ ⟨hr₆, hk₆⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  constructor
  · have ht := linear_update_full (by omega : n + n ≤ 2 * n) hsecond hz25 hr₆ hk₆
    simpa only [one_mul, joined] using ht
  · intro j hj
    change μ₆ j = μ j
    rw [hk₆ j (by omega), hk₅ j (by omega), hk₄ j (by omega), hk₃ j hj.2,
      hk₂ j (by omega), hk₁ j (by omega)]

end Join

section BaseCase

variable {lim : Limits} {P : Program} {d : ℕ}






































end BaseCase

















































































































section RecursiveExecution

variable {lim : Limits} {P : Program} {pSelf pHalf pLinear pFill : ℕ}











































































































































end RecursiveExecution

section CompleteProcedure

variable {lim : Limits} {P : Program} {pSelf pHalf pLinear pFill : ℕ}




















































































end CompleteProcedure

end ThreeSum.LightKaratsuba

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d pLinear pFill : Nat},
  @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pLinear)
      (@Option.some.{0} Light.Stmt ThreeSum.LightArray.linearBody) →
    @Eq.{1} (Option.{0} Light.Stmt)
        (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
          (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
          (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pFill)
        (@Option.some.{0} Light.Stmt Light.fillBody) →
      ∀ {μ : Nat → Int} {n half a b out work U : Nat} {r : Int},
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
          @Eq.{1} Nat
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) half)
              n →
            @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
              @LE.le.{0} Nat instLENat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) out
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
                  work →
                @LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) n))
                    lim.space →
                  @LE.le.{0} Int Int.instLEInt
                      (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                        (@OfNat.ofNat.{0} Int (nat_lit 10) (@instOfNat (nat_lit 10)))
                        (@Nat.cast.{0} Int instNatCastInt U))
                      lim.word →
                    (∀ (i : Nat),
                        @LT.lt.{0} Nat instLTNat i n →
                          And
                            (@LE.le.{0} Int Int.instLEInt
                              (@abs.{0} Int instLatticeInt Int.instAddGroup
                                (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work i)))
                              (@Nat.cast.{0} Int instNatCastInt U))
                            (And
                              (@LE.le.{0} Int Int.instLEInt
                                (@abs.{0} Int instLatticeInt Int.instAddGroup
                                  (μ
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work n) i)))
                                (@Nat.cast.{0} Int instNatCastInt U))
                              (@LE.le.{0} Int Int.instLEInt
                                (@abs.{0} Int instLatticeInt Int.instAddGroup
                                  (μ
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
                                      i)))
                                (@Nat.cast.{0} Int instNatCastInt U)))) →
                      @LT.lt.{0} Nat instLTNat d lim.depth →
                        Light.Ends lim P d (ThreeSum.LightKaratsuba.joinBody pLinear pFill)
                          {
                            loc :=
                              Light.frame
                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt b)
                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt out)
                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt half)
                                            (@List.cons.{0} Int r (@List.nil.{0} Int)))))))),
                            mem := μ }
                          (ThreeSum.LightKaratsuba.joinTime n) fun (σ' : Light.State) =>
                          And
                            (∀ (j : Nat),
                              @LT.lt.{0} Nat instLTNat j
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n) →
                                @Eq.{1} Int
                                  (σ'.mem (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) out j))
                                  (ThreeSum.LightKaratsuba.joined μ work n half j))
                            (Light.KeptBut μ σ'.mem work out
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)) := by
  exact @ThreeSum.LightKaratsuba.join_ends_sourceProof

#print axioms solution
