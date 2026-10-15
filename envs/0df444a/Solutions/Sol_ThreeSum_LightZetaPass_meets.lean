-- Prove2me | solution 1 for ThreeSum.LightZetaPass.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:38:26.012986+00:00
-- url     : https://prove2.me/submissions/87db38e1-16a5-4624-8bf7-f4d60af7b72b

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
import Definitions.Def_ThreeSum1962Source_Bundle08
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
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
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_meets
import Theorems.Thm_ThreeSum_LightZetaBatch_meets
import Theorems.Thm_ThreeSum_SubsetAddress_enumerationWork_bound
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

/-- More time and a weaker conclusion. -/
theorem Meets.mono (h : Meets lim P p d vals μ T R) (hT : T ≤ T') (hR : ∀ r μ', R r μ' → R' r μ') :
    Meets lim P p d vals μ T' R' := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, hp, he.mono hT fun _ => hR _ _⟩

/-- A specification holds with every larger bound on the time. -/
theorem Meets.mono_time (h : Meets lim P p d vals μ T R) (hT : T ≤ T' := by omega) :
    Meets lim P p d vals μ T' R :=
  h.mono hT fun _ _ hR => hR












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
# A rectangular Pascal table in the benchmark language

Every coefficient is built once by addition from the preceding row.
The row-major representation supports one multiplication and two additions
per later lookup. No recursive binomial-coefficient evaluation is used.
-/

namespace ThreeSum.LightPascal

open Light

variable {lim : Limits} {P : Program} {d : ℕ}






















































































































































theorem buildTime_bound (L : ℕ) : buildTime L ≤ 1000*(L+1)^2 := by
  unfold buildTime rowTime LightArray.linearTime
  simp only [fillTime]
  nlinarith

end ThreeSum.LightPascal

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

























































































































































theorem subsetRank_lt {L cut : ℕ} {s : Finset (Fin L)} (hs : s.card ≤ cut) :
    subsetRank s < downsetCap L cut := by
  have hm := subsetMask_isMask s
  exact downsetRank_lt hm.1 (hm.2.trans_le hs)







































end ThreeSum.SubsetAddress

end

section


/-!
# Output-sensitive subset-layer enumeration in the benchmark language

The recursive routine writes into consecutive output cells. Empty layers
return immediately; a zero-cardinality layer emits one mask. The two
recursive children share the output buffer and write adjacent, disjoint
segments. No ambient Boolean cube is scanned and no output list is copied.
-/

namespace ThreeSum.LightSubsetEnumeration

open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}












































theorem time_bound (L k : ℕ) :
    time L k ≤ 150*((4*L+1)*L.choose k+1) := by
  exact Nat.mul_le_mul_left 150 (enumerationWork_bound L k)



























































































































































end ThreeSum.LightSubsetEnumeration

end

section


/-!
# A fixed subset-layer enumerator with its own power-table construction

The main theorem has no supplied lookup-table correctness assumption. The
only auxiliary memory is a table of `L+1` powers of two, built once before
the recursive enumeration. The output has exactly `L.choose k` cells.
-/

namespace ThreeSum.LightSubsetEnumerationSetup

open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}


































































theorem time_bound (L k : ℕ) : time L k ≤ 800*(L+1)*(L.choose k+1) := by
  have h := LightSubsetEnumeration.time_bound L k
  unfold time powTableTime
  nlinarith

end ThreeSum.LightSubsetEnumerationSetup

end

section


/-!
# A complete subset-rank program, including table construction

This fixed program constructs both lookup tables in scratch and then ranks
one valid mask. Its cost is quadratic in the bit width. The faster cached
rank contract remains available separately, but no supplied table correctness
assumption appears in the fixed-program result below.
-/

namespace ThreeSum.LightSubsetSetup

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}
















































































theorem time_bound (L : ℕ) : time L ≤ 1200*(L+1)^2 := by
  have hb := buildTime_bound L
  unfold time powTableTime rankTime
  nlinarith

end ThreeSum.LightSubsetSetup

end

section


/-!
# An actual compact-table zeta-cell update

The fixed procedure builds its own Pascal and power tables, ranks the input
mask, deletes the requested coordinate, ranks the smaller mask if necessary,
and writes the zeta addition at the compact downset address. The scratch area
is polynomial in the width. Neither addresses nor table values are supplied
by an oracle.
-/

namespace ThreeSum.LightZetaCell

open Light ThreeSum.SubsetAddress ThreeSum.MaskErase
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}



































































































































































theorem time_bound (L : ℕ) : time L ≤ 2000*(L+1)^2 := by
  have h := LightSubsetSetup.time_bound L
  unfold time LightMaskErase.time LightSubsetOffset.time rankTime
  nlinarith

end ThreeSum.LightZetaCell

end

section


/-!
# A compact layer pass of zeta updates

The input masks occupy an actual memory segment. Each loop iteration
loads one mask and invokes the verified compact-cell routine. The source
and mask segments are preserved, and all destination entries omitted
from the mask list retain their previous values. There is no scan of
the ambient cube in this procedure.
-/

namespace ThreeSum.LightZetaBatch

open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.MaskDecode

variable {lim : Limits} {P : Program}












































































































theorem values_layer {L cardinal : ℕ} (μ : ℕ → ℤ) (dst : ℕ)
    (a : Fin L) (f : Finset (Fin L) → ℤ) (S : Finset (Fin L)) :
    values μ dst (enumerateLayer L cardinal) a f S =
      if S.card = cardinal then Subset.zetaStep a f S else μ (dst+subsetRank S) := by
  have hm := subsetMask_isMask S
  simp only [values,mem_enumerateLayer,IsMask,hm.1,true_and,hm.2]

theorem time_bound (L n : ℕ) : time L n ≤ 2100*(L+1)^2*(n+1) := by
  have h := LightZetaCell.time_bound L
  have hmul := Nat.mul_le_mul_left n h
  have hpoly : 1 ≤ (L+1)^2 := Nat.one_le_pow' 2 L
  have hsmall := Nat.mul_le_mul_left n (show 40 ≤ 100*(L+1)^2 by omega)
  unfold time
  nlinarith

end ThreeSum.LightZetaBatch

end

section


/-!
# A complete coordinate pass over a compact downset

For each stored cardinality the fixed procedure constructs its layer of
masks, then runs the compact-cell update on that layer. Only the compact
downset and polynomial workspace are allocated; the program never visits
all integers below `2^L`. The source table remains unchanged throughout
the pass.
-/

namespace ThreeSum.LightZetaPass

open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}





theorem choose_le_cap {L cut j : ℕ} (hcut : cut ≤ L) (hj : j ≤ cut) :
    L.choose j ≤ downsetCap L cut := by
  have ho := layerOffset_mono L (show j+1 ≤ min cut L+1 by omega)
  rw [layerOffset_succ] at ho
  unfold downsetCap
  omega























theorem meets_sourceProof
    {pMain pEnumSetup pEnum pBatch pCell pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ}
    (hmain : P[pMain]? = some (body pEnumSetup pBatch))
    (hEnumSetup : P[pEnumSetup]? = some (LightSubsetEnumerationSetup.body pPowers pEnum))
    (hEnum : P[pEnum]? = some (LightSubsetEnumeration.body pEnum))
    (hBatch : P[pBatch]? = some (LightZetaBatch.body pCell))
    (hCell : P[pCell]? = some (LightZetaCell.body pSetup pOffset pErase pRank))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body)
    (hErase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L cut src dst maskBase work U d : ℕ}
    (a : Fin L) (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hcut : cut ≤ L)
    (hsrc : src+downsetCap L cut ≤ maskBase) (hdst : dst+downsetCap L cut ≤ maskBase)
    (hmasks : maskBase+downsetCap L cut ≤ work)
    (hsep : Apart src (downsetCap L cut) dst (downsetCap L cut))
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : 2*(U : ℤ) ≤ lim.word)
    (hread : TableAt μ src cut f) (hvalues : ∀ T, T.card ≤ cut → |f T| ≤ U)
    (hd : d+L+6 ≤ lim.depth) :
    Meets lim P pMain d [L,cut,a.val,src,dst,maskBase,work] μ (time L cut)
      (fun _ μ' => TableAt μ' dst cut (Subset.zetaStep a f) ∧
        KeptBut μ μ' maskBase dst (downsetCap L cut)) := by
  have hword₀ : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : (2^(L+1) : ℕ) ≤ (L+1)*2^(L+1) := Nat.le_mul_of_pos_left _ (by omega)
    exact (by exact_mod_cast hh : ((2^(L+1) : ℕ) : ℤ) ≤
      (((L+1)*2^(L+1) : ℕ) : ℤ)).trans hword
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ cut src dst maskBase work a f)
    (cut+1) (roundBudget L cut) ?start ?round ?done ?bound
    (hT := by first
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
    refine ⟨0,0,μ,?_,SameOn.refl,?_⟩
    · simp [update_frame_setLocal]
      change frame [(L : ℤ),cut,a.val,src,dst,maskBase,work,0] =
        frame ([(L : ℤ),cut,a.val,src,dst,maskBase,work,0] ++ [0,0])
      exact (frame_append_zeros _ 2).symm
    · intro S hS
      simp [stageValues]
  case round =>
    rintro j _ hj _ ⟨n,r,μ',rfl,hkept,hout⟩
    have hjcut : j ≤ cut := by omega
    have hchoose := choose_le_cap hcut hjcut
    have hsource : TableAt μ' src cut f := by
      intro T hT
      have hr := subsetRank_lt hT
      exact (hkept _ ⟨by omega,by omega⟩).trans (hread T hT)
    have hen := LightSubsetEnumerationSetup.meets (d := d+1) hEnumSetup C.powers hEnum
      (μ := μ') (L := L) (k := j) (dst := maskBase) (work := work)
      hw (by omega) hword₀ (by omega) (by omega) (by omega)
    have hentime : LightSubsetEnumerationSetup.time L j ≤ enumBudget L cut := by
      exact (LightSubsetEnumerationSetup.time_bound L j).trans
        (Nat.mul_le_mul_left (800*(L+1)) (Nat.succ_le_succ hchoose))
    unfold roundBody roundBudget
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
            Light.Ends.callToThen ((hen.mono_time hentime) _ (by omega)) ?_ ?_ ?_ ?_
        | refine Light.Ends.callToThen (hen.mono_time hentime) ?_ ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  enumBudget, batchBudget]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [enumBudget, batchBudget] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 => omega);
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, enumBudget, batchBudget] <;>
                omega)));
      (on_goal -1 =>
          ((rintro count μ₁ ⟨hcount, hseg, hpowers, henkept⟩);
            (try with_unfolding_none refine Light.Ends.skip ?_)))
    have hsource₁ : TableAt μ₁ src cut f := by
      intro T hT
      have hr := subsetRank_lt hT
      exact (henkept _ ⟨by omega,Or.inl (by omega)⟩).trans (hsource T hT)
    have hb := LightZetaBatch.meets (d := d+1) hBatch hCell C hOffset hErase
      (enumerateLayer L j) a f hw (by omega) (by omega)
      (by rw [enumerateLayer_length]; omega) hsep
      (Or.inr hdst) hspace hword hvalueWord hsource₁ hvalues hseg
      (fun m hm => (mem_enumerateLayer L j m).mp hm) hjcut (by omega)
    have hbtime : LightZetaBatch.time L (enumerateLayer L j).length ≤ batchBudget L cut := by
      rw [enumerateLayer_length]
      exact (LightZetaBatch.time_bound L (L.choose j)).trans
        (Nat.mul_le_mul_left (2100*(L+1)^2) (Nat.succ_le_succ hchoose))
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
            Light.Ends.callToThen ((hb.mono_time hbtime) _ (by omega)) ?_ ?_ ?_ ?_
        | refine Light.Ends.callToThen (hb.mono_time hbtime) ?_ ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hcount,
                  enumerateLayer_length, enumBudget, batchBudget]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hcount, enumerateLayer_length, enumBudget, batchBudget] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 => omega);
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hcount,
                  enumerateLayer_length, enumBudget, batchBudget] <;>
                omega)));
      (on_goal -1 =>
          ((rintro res μ₂ ⟨hnew, hbkept⟩);
            (try with_unfolding_none refine Light.Ends.skip ?_)))
    refine ⟨by simp,count,res,μ₂,?_,?_,?_⟩
    · simp [update_frame_setLocal]
    · intro i hi
      exact (hbkept i ⟨by omega,hi.2⟩).trans
        ((henkept i ⟨by omega,Or.inl hi.1⟩).trans (hkept i hi))
    · intro T hT
      have hr := subsetRank_lt hT
      have hn := hnew T hT
      rw [LightZetaBatch.values_layer] at hn
      have hbefore : μ₁ (dst+subsetRank T) = μ' (dst+subsetRank T) :=
        henkept _ ⟨by omega,Or.inl (by omega)⟩
      by_cases heq : T.card = j
      · have hlt : T.card < j+1 := by omega
        simpa only [stageValues,heq,ite_true,show j < j+1 by omega] using hn
      · rw [if_neg heq,hbefore,hout T hT] at hn
        have hlt : T.card < j+1 ↔ T.card < j := by omega
        simpa only [stageValues,hlt] using hn
  case done =>
    rintro _ _ ⟨n,r,μ',rfl,hkept,hout⟩
    refine ⟨?_,hkept⟩
    intro T hT
    simpa only [stageValues,show T.card < cut+1 by omega,ite_true] using hout T hT
  case bound =>
    rintro j _ hj _ ⟨n,r,μ',rfl,_,_⟩
    (((try have := Light.Std.space_le (by assumption)));
      ((try have := Light.Std.const_le (by assumption)));
      (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))



















































end ThreeSum.LightZetaPass

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program}
  {pMain pEnumSetup pEnum pBatch pCell pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : Nat},
  @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMain)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightZetaPass.body pEnumSetup pBatch)) →
    @Eq.{1} (Option.{0} Light.Stmt)
        (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
          (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
          (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pEnumSetup)
        (@Option.some.{0} Light.Stmt (ThreeSum.LightSubsetEnumerationSetup.body pPowers pEnum)) →
      @Eq.{1} (Option.{0} Light.Stmt)
          (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
            (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
            (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pEnum)
          (@Option.some.{0} Light.Stmt (ThreeSum.LightSubsetEnumeration.body pEnum)) →
        @Eq.{1} (Option.{0} Light.Stmt)
            (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
              (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
              (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pBatch)
            (@Option.some.{0} Light.Stmt (ThreeSum.LightZetaBatch.body pCell)) →
          @Eq.{1} (Option.{0} Light.Stmt)
              (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
                (fun (as : List.{0} Light.Stmt) (i : Nat) =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
                (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pCell)
              (@Option.some.{0} Light.Stmt (ThreeSum.LightZetaCell.body pSetup pOffset pErase pRank)) →
            ThreeSum.LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank →
              @Eq.{1} (Option.{0} Light.Stmt)
                  (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
                    (fun (as : List.{0} Light.Stmt) (i : Nat) =>
                      @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
                    (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pOffset)
                  (@Option.some.{0} Light.Stmt ThreeSum.LightSubsetOffset.body) →
                @Eq.{1} (Option.{0} Light.Stmt)
                    (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
                      (fun (as : List.{0} Light.Stmt) (i : Nat) =>
                        @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
                      (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pErase)
                    (@Option.some.{0} Light.Stmt (ThreeSum.LightMaskErase.body pErase)) →
                  ∀ {μ : Nat → Int} {L cut src dst maskBase work U d : Nat} (a : Fin L) (f : Finset.{0} (Fin L) → Int),
                    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
                      @LE.le.{0} Nat instLENat cut L →
                        @LE.le.{0} Nat instLENat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src
                              (ThreeSum.SubsetAddress.downsetCap L cut))
                            maskBase →
                          @LE.le.{0} Nat instLENat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
                                (ThreeSum.SubsetAddress.downsetCap L cut))
                              maskBase →
                            @LE.le.{0} Nat instLENat
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maskBase
                                  (ThreeSum.SubsetAddress.downsetCap L cut))
                                work →
                              Light.Apart src (ThreeSum.SubsetAddress.downsetCap L cut) dst
                                  (ThreeSum.SubsetAddress.downsetCap L cut) →
                                @LE.le.{0} Nat instLENat
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
                                        (ThreeSum.LightPascal.tableSize L))
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) L
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    lim.space →
                                  @LE.le.{0} Int Int.instLEInt
                                      (@Nat.cast.{0} Int instNatCastInt
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) L
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) L
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                                      lim.word →
                                    @LE.le.{0} Int Int.instLEInt
                                        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                                          (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))
                                          (@Nat.cast.{0} Int instNatCastInt U))
                                        lim.word →
                                      @ThreeSum.LightZetaCell.TableAt L μ src cut f →
                                        (∀ (T : Finset.{0} (Fin L)),
                                            @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin L) T) cut →
                                              @LE.le.{0} Int Int.instLEInt
                                                (@abs.{0} Int instLatticeInt Int.instAddGroup (f T))
                                                (@Nat.cast.{0} Int instNatCastInt U)) →
                                          @LE.le.{0} Nat instLENat
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d L)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                                              lim.depth →
                                            Light.Meets lim P pMain d
                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cut)
                                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@Fin.val L a))
                                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
                                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
                                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt maskBase)
                                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                                            (@List.nil.{0} Int))))))))
                                              μ (ThreeSum.LightZetaPass.time L cut) fun (x : Int) (μ' : Nat → Int) =>
                                              And
                                                (@ThreeSum.LightZetaCell.TableAt L μ' dst cut
                                                  (@ThreeSum.Subset.zetaStep.{0} (Fin L) (instDecidableEqFin L) a f))
                                                (Light.KeptBut μ μ' maskBase dst
                                                  (ThreeSum.SubsetAddress.downsetCap L cut)) := by
  exact @ThreeSum.LightZetaPass.meets_sourceProof

#print axioms solution
