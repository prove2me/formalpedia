-- Prove2me | solution 1 for ThreeSum.LightColorClasses.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:18:23.204571+00:00
-- url     : https://prove2.me/submissions/aa28714b-23cb-4a0f-a022-1a6df86dedb7

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
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
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
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum_LightClassFilter_meets
import Theorems.Thm_ThreeSum_LightColorArray_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSumApsp
end ThreeSumApsp

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































































/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]

















































/-- A segment that does not meet the region is kept. -/
theorem Seg.of_sameOutside (h : Seg μ b l) (hs : SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : Seg μ' b l :=
  h.congr fun i hi => hs _ (by omega)












































































end Light

end
end

section


/-!
# Stable extraction of one color class from the original signed array

The program reads stored colors and original values. It writes a length
header followed by exactly the selected values, optionally negated. Repeated
values are preserved; deduplication belongs to the later normalization pass.
-/

namespace ThreeSum.LightClassFilter

open Light

set_option maxHeartbeats 1200000












theorem items_length_le (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) :
    (items x color want scale n).length ≤ n := by
  simpa only [items,List.length_map,List.length_range] using
    List.length_filter_le (p := fun i => decide (color i = want)) (l := List.range n)

























variable {lim : Limits} {P : Program} {d : ℕ}























































































end ThreeSum.LightClassFilter

end

section


/-!
# Actual evaluation of one member of the deterministic coloring family

Two calls to the checked mask-coordinate routine inspect the selected bits
of an original array index. Four literal color arguments determine the map
from bit patterns to the three colors. The cost is linear in the binary
width and independent of the numeric index magnitude.
-/

namespace ThreeSum.LightColorIndex

open Light LightSubsetAddress

variable {lim : Limits} {P : Program}












theorem color_lt {W : ℕ} (p : Coloring.Parameter W) (m : ℕ) : color p m < 3 :=
  (p.2 _).isLt





























































































end ThreeSum.LightColorIndex

end

section


/-!
# Exact original-position semantics of the constructed color-class lists

The machine keeps repeated values within a class and negates the third
class. The list membership witnesses are original positions. Any binary
width large enough for the indices suffices for the deterministic family.
-/

namespace ThreeSum.ColorClassLists

open LightClassFilter



@[simp] theorem value_fin {n : ℕ} (x : Fin n → ℤ) (i : Fin n) : value x i.val = x i := by
  simp [value,i.isLt]































theorem length_classList_le {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (c : ℕ) (scale : ℤ) : (classList p x c scale).length ≤ n :=
  items_length_le ..



































































end ThreeSum.ColorClassLists

end

section


/-!
# Original-array construction of all three color classes

A fixed six-procedure program builds the color array and extracts three
disjoint output segments with length headers. The third class is negated.
Original values and their multiplicities are kept until class normalization.
-/

namespace ThreeSum.LightColorClasses

open Light ColorClassLists

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000



































variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets_sourceProof {pMain src n W colors dst0 dst1 dst2 work U : ℕ} {μ : ℕ → ℤ}
    (C : Procs P pMain) (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : n ≤ 2^W)
    (hsrc : src+n ≤ colors) (hcolors : colors+n ≤ dst0)
    (h0 : dst0+(n+1) ≤ dst1) (h1 : dst1+(n+1) ≤ dst2) (h2 : dst2+(n+1) ≤ work)
    (hspace : work+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word) (hU : (U : ℤ) ≤ lim.word)
    (hd : d+W+3 ≤ lim.depth) (hread : Seg μ src (List.ofFn x))
    (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    Meets lim P pMain d [src,n,W,p.1.1.val,p.1.2.val,(p.2 (false,false)).val,
      (p.2 (false,true)).val,(p.2 (true,false)).val,(p.2 (true,true)).val,
      colors,dst0,dst1,dst2,work] μ (time W n)
      (fun _ ν => Output p x μ ν colors dst0 dst1 dst2) := by
  have hW := p.1.1.isLt
  have h3 : (3 : ℤ) ≤ lim.word := by
    have hh : 2^2 ≤ 2^(W+1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hh' : (4 : ℤ) ≤ ((2^(W+1) : ℕ) : ℤ) := by exact_mod_cast hh
    omega
  have read : ∀ i < n, μ (src+i) = value x i := by
    intro i hi
    have hh := hread i (by simpa using hi)
    simpa only [List.getElem_ofFn,← value_fin x ⟨i,hi⟩] using hh
  have bound : ∀ i < n, |value x i| ≤ (U : ℤ) := by
    intro i hi
    simpa only [value,hi,dite_true] using hbound ⟨i,hi⟩
  have len0 := length_classList_le p x 0 1
  have len1 := length_classList_le p x 1 1
  apply Meets.of_body C.main
  unfold body time
  have hc := LightColorArray.meets (d := d+1) (n := n) (dst := colors) (work := work)
    C.colors C.powers C.color C.erase μ p hw hn (by omega) hspace hword (by omega)
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
                LightColorArray.time, LightColorIndex.time, LightMaskErase.time,
                LightClassFilter.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightColorArray.time, LightColorIndex.time, LightMaskErase.time,
                LightClassFilter.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, LightColorArray.time,
                LightColorIndex.time, LightMaskErase.time,
                LightClassFilter.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro r ν₁ ⟨color₁, _, keep₁⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have read₁ : ∀ i < n, ν₁ (src+i) = value x i := by
    intro i hi
    exact (keep₁ _ ⟨by omega,Or.inl (by omega)⟩).trans (read i hi)
  have hf0 := LightClassFilter.meets (d := d+1) (μ := ν₁) (src := src) (colors := colors)
    (dst := dst0) (n := n) (want := 0) (scale := 1) (U := U) C.filter
    (value x) (LightColorIndex.color p) hw h3 (by omega) hcolors (by omega)
    (by decide) (by norm_num) hU read₁ color₁ (fun i _ => LightColorIndex.color_lt p i) bound
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
      | refine Light.Ends.callToThen (hf0 _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hf0 ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightColorArray.time, LightColorIndex.time, LightMaskErase.time,
                LightClassFilter.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightColorArray.time, LightColorIndex.time, LightMaskErase.time,
                LightClassFilter.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, LightColorArray.time,
                LightColorIndex.time, LightMaskErase.time,
                LightClassFilter.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro r ν₂ ⟨_, header0, values0, keep₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have read₂ : ∀ i < n, ν₂ (src+i) = value x i := by
    intro i hi
    exact (keep₂ _ (Or.inl (by omega))).trans (read₁ i hi)
  have color₂ : ∀ i < n, ν₂ (colors+i) = (LightColorIndex.color p i : ℤ) := by
    intro i hi
    exact (keep₂ _ (Or.inl (by omega))).trans (color₁ i hi)
  have hf1 := LightClassFilter.meets (d := d+1) (μ := ν₂) (src := src) (colors := colors)
    (dst := dst1) (n := n) (want := 1) (scale := 1) (U := U) C.filter
    (value x) (LightColorIndex.color p) hw h3 (by omega) (by omega) (by omega)
    (by decide) (by norm_num) hU read₂ color₂ (fun i _ => LightColorIndex.color_lt p i) bound
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
      | refine Light.Ends.callToThen (hf1 _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hf1 ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightColorArray.time, LightColorIndex.time, LightMaskErase.time,
                LightClassFilter.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightColorArray.time, LightColorIndex.time, LightMaskErase.time,
                LightClassFilter.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, LightColorArray.time,
                LightColorIndex.time, LightMaskErase.time,
                LightClassFilter.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro r ν₃ ⟨_, header1, values1, keep₃⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have read₃ : ∀ i < n, ν₃ (src+i) = value x i := by
    intro i hi
    exact (keep₃ _ (Or.inl (by omega))).trans (read₂ i hi)
  have color₃ : ∀ i < n, ν₃ (colors+i) = (LightColorIndex.color p i : ℤ) := by
    intro i hi
    exact (keep₃ _ (Or.inl (by omega))).trans (color₂ i hi)
  have hf2 := LightClassFilter.meets (d := d+1) (μ := ν₃) (src := src) (colors := colors)
    (dst := dst2) (n := n) (want := 2) (scale := -1) (U := U) C.filter
    (value x) (LightColorIndex.color p) hw h3 (by omega) (by omega) (by omega)
    (by decide) (by norm_num) hU read₃ color₃ (fun i _ => LightColorIndex.color_lt p i) bound
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
      | refine Light.Ends.callToThen (hf2 _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hf2 ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightColorArray.time, LightColorIndex.time, LightMaskErase.time,
                LightClassFilter.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightColorArray.time, LightColorIndex.time, LightMaskErase.time,
                LightClassFilter.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, LightColorArray.time,
                LightColorIndex.time, LightMaskErase.time,
                LightClassFilter.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro r ν₄ ⟨_, header2, values2, keep₄⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  refine ⟨?_,?_,?_,?_,?_,header2,values2,?_⟩
  · intro i hi
    exact (keep₄ _ (Or.inl (by omega))).trans (color₃ i hi)
  · exact (keep₄ _ (Or.inl (by omega))).trans
      ((keep₃ _ (Or.inl (by omega))).trans header0)
  · exact (values0.of_sameOutside keep₃ (Or.inl (by change dst0+1+(classList p x 0 1).length ≤ dst1; omega))).of_sameOutside
      keep₄ (Or.inl (by change dst0+1+(classList p x 0 1).length ≤ dst2; omega))
  · exact (keep₄ _ (Or.inl (by omega))).trans header1
  · exact values1.of_sameOutside keep₄ (Or.inl (by change dst1+1+(classList p x 1 1).length ≤ dst2; omega))
  · intro a ha
    exact (keep₄ _ (Or.inl (by omega))).trans
      ((keep₃ _ (Or.inl (by omega))).trans
        ((keep₂ _ (Or.inl (by omega))).trans (keep₁ _ ⟨by omega,Or.inl ha⟩)))



























end ThreeSum.LightColorClasses

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain src n W colors dst0 dst1 dst2 work U : Nat} {μ : Nat → Int}
  (C : ThreeSum.LightColorClasses.Procs P pMain) (p : ThreeSum.Coloring.Parameter W) (x : Fin n → Int),
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    @LE.le.{0} Nat instLENat n
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) W) →
      @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src n) colors →
        @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) colors n) dst0 →
          @LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst0
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              dst1 →
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst1
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                dst2 →
              @LE.le.{0} Nat instLENat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst2
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  work →
                @LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) W
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    lim.space →
                  @LE.le.{0} Int Int.instLEInt
                      (@Nat.cast.{0} Int instNatCastInt
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) W
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                      lim.word →
                    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt U) lim.word →
                      @LE.le.{0} Nat instLENat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d W)
                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          lim.depth →
                        Light.Seg μ src (@List.ofFn.{0} Int n x) →
                          (∀ (i : Fin n),
                              @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (x i))
                                (@Nat.cast.{0} Int instNatCastInt U)) →
                            Light.Meets lim P pMain d
                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt W)
                                    (@List.cons.{0} Int
                                      (@Nat.cast.{0} Int instNatCastInt
                                        (@Fin.val W
                                          (@Prod.fst.{0, 0} (Fin W) (Fin W)
                                            (@Prod.fst.{0, 0} (Prod.{0, 0} (Fin W) (Fin W))
                                              (Prod.{0, 0} Bool Bool →
                                                Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                              p))))
                                      (@List.cons.{0} Int
                                        (@Nat.cast.{0} Int instNatCastInt
                                          (@Fin.val W
                                            (@Prod.snd.{0, 0} (Fin W) (Fin W)
                                              (@Prod.fst.{0, 0} (Prod.{0, 0} (Fin W) (Fin W))
                                                (Prod.{0, 0} Bool Bool →
                                                  Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                p))))
                                        (@List.cons.{0} Int
                                          (@Nat.cast.{0} Int instNatCastInt
                                            (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                              (@Prod.snd.{0, 0} (Prod.{0, 0} (Fin W) (Fin W))
                                                (Prod.{0, 0} Bool Bool →
                                                  Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                p (@Prod.mk.{0, 0} Bool Bool Bool.false Bool.false))))
                                          (@List.cons.{0} Int
                                            (@Nat.cast.{0} Int instNatCastInt
                                              (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                                (@Prod.snd.{0, 0} (Prod.{0, 0} (Fin W) (Fin W))
                                                  (Prod.{0, 0} Bool Bool →
                                                    Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                  p (@Prod.mk.{0, 0} Bool Bool Bool.false Bool.true))))
                                            (@List.cons.{0} Int
                                              (@Nat.cast.{0} Int instNatCastInt
                                                (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                                  (@Prod.snd.{0, 0} (Prod.{0, 0} (Fin W) (Fin W))
                                                    (Prod.{0, 0} Bool Bool →
                                                      Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                    p (@Prod.mk.{0, 0} Bool Bool Bool.true Bool.false))))
                                              (@List.cons.{0} Int
                                                (@Nat.cast.{0} Int instNatCastInt
                                                  (@Fin.val
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                                    (@Prod.snd.{0, 0} (Prod.{0, 0} (Fin W) (Fin W))
                                                      (Prod.{0, 0} Bool Bool →
                                                        Fin
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                      p (@Prod.mk.{0, 0} Bool Bool Bool.true Bool.true))))
                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt colors)
                                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst0)
                                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst1)
                                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst2)
                                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                                          (@List.nil.{0} Int)))))))))))))))
                              μ (ThreeSum.LightColorClasses.time W n) fun (x_1 : Int) (ν : Nat → Int) =>
                              @ThreeSum.LightColorClasses.Output n W p x μ ν colors dst0 dst1 dst2 := by
  exact @ThreeSum.LightColorClasses.Procs.meets_sourceProof

#print axioms solution
