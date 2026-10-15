-- Prove2me | solution 1 for ThreeSum.LightColorBands.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:37:52.404666+00:00
-- url     : https://prove2.me/submissions/f5a3f56a-de2a-4ef7-a855-fe7e8105f8e3

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
import Definitions.Def_ThreeSum1962Source_Bundle04
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
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
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
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_LightBandPreprocessing_Procs_meets
import Theorems.Thm_ThreeSum_LightBandPreprocessing_time_bound
import Theorems.Thm_ThreeSum_LightColorClasses_Procs_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress

section


/-!
# Consecutive bands of a strictly increasing array

The last band is truncated. Every input position belongs to its quotient
band, the bands are strictly separated, and each band has at most `g` entries.
The quotient in these specifications is realized by `LightBandPartition`.
-/

namespace ThreeSum.BandPartition












theorem size_mono {n m g : ℕ} (h : n ≤ m) : size n g ≤ size m g := by
  by_cases hn : n = 0
  · simp [size,hn]
  · have hm : m ≠ 0 := by omega
    have hd := Nat.div_le_div_right (c := g) (show n-1 ≤ m-1 by omega)
    simp only [size,if_neg hn,if_neg hm]
    omega
























































































end ThreeSum.BandPartition

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
# A closed machine program listing all relevant sorted-band candidates

The program computes its own binary width and power table, then executes
exactly the three rectangular owner tables. Every table cell contains an
interval lookup result (index plus one, zero for a miss). The source arrays
remain intact. The coverage theorem below connects these actual memory cells
to every relevant triple, and hence to every exact equation in the bands.
-/

namespace ThreeSum.LightBandEnumeration

set_option maxHeartbeats 1200000
set_option maxRecDepth 4000

open Light ThreeSum.BandEnumeration ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

























































































































































































































































































































































theorem count_mono {a b c a' b' c' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    count a b c ≤ count a' b' c' := by
  unfold count
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul hb hc) (Nat.mul_le_mul ha hb))
    (Nat.mul_le_mul ha hc)

theorem width_mono {a b c a' b' c' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    width a b c ≤ width a' b' c' := Nat.clog_mono_right 2 (by omega)









end ThreeSum.LightBandEnumeration

end

section


/-!
# Finite bounds and original-value witness coverage for band preprocessing

These corollaries refer to the memory written by the closed twenty-procedure
program. An exact equation between members of the three original classes
produces a positive owner-table cell and three bands containing the values.
-/

namespace ThreeSum.LightBandPreprocessing

open Light ThreeSum.BandPartition



































































































theorem count_square_bound (a b c g : ℕ) :
    LightBandEnumeration.count (size a g) (size b g) (size c g) ≤
      3*(size (a+b+c) g)^2 := by
  have h := LightBandEnumeration.count_mono (size_mono (g := g) (show a ≤ a+b+c by omega))
    (size_mono (g := g) (show b ≤ a+b+c by omega)) (size_mono (g := g) (show c ≤ a+b+c by omega))
  convert h using 1 <;> unfold LightBandEnumeration.count <;> ring



end ThreeSum.LightBandPreprocessing

end

section


/-! # Uniform band resources for three classes whose lengths sum to n -/

namespace ThreeSum.ColorBandBounds

open BandPartition

set_option maxRecDepth 4000
set_option maxHeartbeats 800000










theorem count_le {a b c n g : ℕ} (hlen : a+b+c=n) :
    LightBandEnumeration.count (size a g) (size b g) (size c g) ≤ count n g := by
  simpa only [count,hlen] using LightBandPreprocessing.count_square_bound a b c g

theorem width_le {a b c n g : ℕ} (hlen : a+b+c=n) :
    LightBandEnumeration.width (size a g) (size b g) (size c g) ≤ width n g :=
  LightBandEnumeration.width_mono (size_mono (by omega : a ≤ n))
    (size_mono (by omega : b ≤ n)) (size_mono (by omega : c ≤ n))

theorem time_le {a b c n g : ℕ} (hlen : a+b+c=n) :
    LightBandPreprocessing.time a b c g ≤ time n g := by
  have ht := LightBandPreprocessing.time_bound a b c g
  have hc := count_le (g := g) hlen
  have hw := width_le (g := g) hlen
  have hp := Nat.mul_le_mul (Nat.mul_le_mul_left 1000
    (show LightBandEnumeration.count (size a g) (size b g) (size c g)+a+b+c+1 ≤
      count n g+n+1 by omega)) (Nat.add_le_add_right hw 1)
  unfold time
  rw [hlen] at ht
  omega

theorem space_le {a b c n g work : ℕ} (hlen : a+b+c=n) :
    LightBandPreprocessing.space work a b c g ≤ space work n g := by
  have hc := count_le (g := g) hlen
  have hw := width_le (g := g) hlen
  unfold LightBandPreprocessing.space space
  omega

theorem word_le {a b c n g U : ℕ} (hlen : a+b+c=n) :
    LightBandPreprocessing.word a b c g U ≤ word n g U := by
  have ha := size_mono (g := g) (by omega : a ≤ n)
  have hb := size_mono (g := g) (by omega : b ≤ n)
  have hc := size_mono (g := g) (by omega : c ≤ n)
  unfold LightBandPreprocessing.word word LightBandEnumeration.word
  omega

theorem depth_le {a b c n g : ℕ} (hlen : a+b+c=n) :
    LightBandPreprocessing.depth a b c g ≤ depth n g := by
  have hw := width_le (g := g) hlen
  unfold LightBandPreprocessing.depth depth
  rw [hlen]
  omega

end ThreeSum.ColorBandBounds

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




@[simp] theorem items_zero (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) :
    items x color want scale 0 = [] := by simp [items]

theorem items_succ (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) :
    items x color want scale (n+1) =
      items x color want scale n ++ (if color n = want then [scale*x n] else []) := by
  by_cases h : color n = want <;> simp [items,List.range_succ,h]

theorem items_length_le (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) :
    (items x color want scale n).length ≤ n := by
  simpa only [items,List.length_map,List.length_range] using
    List.length_filter_le (p := fun i => decide (color i = want)) (l := List.range n)

theorem mem_items (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) (z : ℤ) :
    z ∈ items x color want scale n ↔ ∃ i, i < n ∧ color i = want ∧ scale*x i = z := by
  simp [items,and_assoc]





















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




































theorem length_classList_le {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (c : ℕ) (scale : ℤ) : (classList p x c scale).length ≤ n :=
  items_length_le ..

theorem items_lengths_sum (x : ℕ → ℤ) (color : ℕ → ℕ) (hcolor : ∀ i, color i < 3) (n : ℕ) :
    (items x color 0 1 n).length + (items x color 1 1 n).length +
      (items x color 2 (-1) n).length = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc := hcolor n
    have hc' : color n = 0 ∨ color n = 1 ∨ color n = 2 := by omega
    rcases hc' with he | he | he <;>
      simp only [items_succ,he] <;> norm_num at * <;> omega

theorem class_lengths_sum {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ) :
    (classList p x 0 1).length + (classList p x 1 1).length +
      (classList p x 2 (-1)).length = n :=
  items_lengths_sum _ _ (LightColorIndex.color_lt p) n



















































end ThreeSum.ColorClassLists

end

section


/-!
# Original input to normalized color bands

This fixed program computes index colors, writes the three class arrays and
their headers, then reads those headers into the existing normalization and
owner-table program. All buffers and resource bounds depend on the original
input length, rather than on externally supplied color-class lengths.
-/

namespace ThreeSum.LightColorBands

open Light ColorClassLists

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000













theorem class_bounded {n W U : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (c : ℕ) (scale : ℤ) (hs : |scale| ≤ 1) (hx : ∀ i, |x i| ≤ (U : ℤ)) :
    ∀ z ∈ classList p x c scale, |z| ≤ (U : ℤ) := by
  intro z hz
  obtain ⟨i,hi,_,rfl⟩ :=
    (LightClassFilter.mem_items (value x) (LightColorIndex.color p) c scale n z).mp hz
  have hv : |value x i| ≤ (U : ℤ) := by
    simpa only [value,hi,dite_true] using hx ⟨i,hi⟩
  rw [abs_mul]
  calc
    |scale| * |value x i| ≤ 1 * (U : ℤ) :=
      mul_le_mul hs hv (abs_nonneg _) (by norm_num)
    _ = (U : ℤ) := one_mul _








variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets_sourceProof {pMain src n W colors dst0 dst1 dst2 g av ae bv be cv ce work U : ℕ}
    {μ : ℕ → ℤ} (R : Procs P pMain) (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : n ≤ 2^W) (hg : 0 < g)
    (hsrc : src+n ≤ colors) (hcolors : colors+n ≤ dst0)
    (h0 : dst0+n+1 ≤ dst1) (h1 : dst1+n+1 ≤ dst2) (h2 : dst2+n+1 ≤ av)
    (hav : av+n ≤ ae) (hae : ae+2+2*n ≤ bv)
    (hbv : bv+n ≤ be) (hbe : be+2+2*n ≤ cv)
    (hcv : cv+n ≤ ce) (hce : ce+2+2*n ≤ work)
    (hspace : space work W n g ≤ lim.space)
    (hword : (word W n g U : ℤ) ≤ lim.word) (hd : d+depth W n g ≤ lim.depth)
    (hread : Seg μ src (List.ofFn x)) (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    Meets lim P pMain d [src,n,W,p.1.1.val,p.1.2.val,(p.2 (false,false)).val,
      (p.2 (false,true)).val,(p.2 (true,false)).val,(p.2 (true,true)).val,
      colors,dst0,dst1,dst2,g,av,ae,bv,be,cv,ce,work] μ (time W n g)
      (fun r ν => LightBandPreprocessing.Output ν av ae bv be cv ce work g hg
        (classList p x 0 1) (classList p x 1 1) (classList p x 2 (-1)) r ∧
          Kept μ ν colors) := by
  have len0 := length_classList_le p x 0 1
  have len1 := length_classList_le p x 1 1
  have len2 := length_classList_le p x 2 (-1)
  have lens := class_lengths_sum p x
  have hs : work+(W+1) ≤ lim.space := by
    unfold space ColorBandBounds.space at hspace
    omega
  have hp : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (show 2^(W+1) ≤ word W n g U by
      unfold word; omega)).trans hword
  have hU : (U : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (show U ≤ word W n g U by
      unfold word; omega)).trans hword
  have hcDepth : d+1+W+3 ≤ lim.depth := by unfold depth at hd; omega
  have hsBand : LightBandPreprocessing.space work
      (classList p x 0 1).length (classList p x 1 1).length
      (classList p x 2 (-1)).length g ≤ lim.space := by
    have hh := ColorBandBounds.space_le (work := work) (g := g) lens
    unfold space at hspace
    omega
  have hwBand : (LightBandPreprocessing.word
      (classList p x 0 1).length (classList p x 1 1).length
      (classList p x 2 (-1)).length g U : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr ((ColorBandBounds.word_le (g := g) (U := U) lens).trans
      (show ColorBandBounds.word n g U ≤ word W n g U by unfold word; omega))).trans hword
  have hdBand : d+1+LightBandPreprocessing.depth
      (classList p x 0 1).length (classList p x 1 1).length
      (classList p x 2 (-1)).length g ≤ lim.depth := by
    have hh := ColorBandBounds.depth_le (g := g) lens
    unfold depth at hd
    omega
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
    (first
      |
        refine
          Light.Ends.callToThen
            ((R.classes.meets (d := d + 1) p x hw hn hsrc hcolors (by omega)
                (by omega) (by omega) hs hp hU hcDepth hread hbound)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (R.classes.meets (d := d + 1) p x hw hn hsrc hcolors (by omega)
              (by omega) (by omega) hs hp hU hcDepth hread hbound)
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightColorClasses.time, LightColorArray.time,
                LightColorIndex.time, LightMaskErase.time,
                LightClassFilter.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightColorClasses.time, LightColorArray.time,
                LightColorIndex.time, LightMaskErase.time,
                LightClassFilter.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, LightColorClasses.time,
                LightColorArray.time, LightColorIndex.time, LightMaskErase.time,
                LightClassFilter.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro r ν₁ hclasses);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have h0Read := hclasses.header0
  have h1Read := hclasses.header1
  have h2Read := hclasses.header2
  have hb := R.bands.meets (d := d+1) (srcA := dst0+1) (srcB := dst1+1) (srcC := dst2+1)
    (av := av) (ae := ae) (bv := bv) (be := be) (cv := cv) (ce := ce) (work := work)
    hw hg (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hsBand hwBand hdBand
    hclasses.values0 hclasses.values1 hclasses.values2
    (class_bounded p x 0 1 (by norm_num) hbound)
    (class_bounded p x 1 1 (by norm_num) hbound)
    (class_bounded p x 2 (-1) (by norm_num) hbound)
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
            ((hb.mono_time (ColorBandBounds.time_le (g := g) lens)) _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (hb.mono_time (ColorBandBounds.time_le (g := g) lens)) ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h0Read,
                h1Read, h2Read, LightColorClasses.time, LightColorArray.time,
                LightColorIndex.time, LightMaskErase.time,
                LightClassFilter.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [h0Read, h1Read, h2Read, LightColorClasses.time,
                LightColorArray.time, LightColorIndex.time, LightMaskErase.time,
                LightClassFilter.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, h0Read, h1Read, h2Read,
                LightColorClasses.time, LightColorArray.time,
                LightColorIndex.time, LightMaskErase.time,
                LightClassFilter.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro result ν₂ ⟨hout, hkeep⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  refine ⟨hout,?_⟩
  intro a ha
  exact (hkeep a (by omega)).trans (hclasses.kept a ha)















































end ThreeSum.LightColorBands

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain src n W colors dst0 dst1 dst2 g av ae bv be cv ce work U : Nat}
  {μ : Nat → Int} (R : ThreeSum.LightColorBands.Procs P pMain) (p : ThreeSum.Coloring.Parameter W) (x : Fin n → Int),
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    @LE.le.{0} Nat instLENat n
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) W) →
      ∀ (hg : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) g),
        @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src n) colors →
          @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) colors n) dst0 →
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst0 n)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                dst1 →
              @LE.le.{0} Nat instLENat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst1 n)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  dst2 →
                @LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst2 n)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    av →
                  @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) av n) ae →
                    @LE.le.{0} Nat instLENat
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ae
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
                        bv →
                      @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bv n)
                          be →
                        @LE.le.{0} Nat instLENat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) be
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
                            cv →
                          @LE.le.{0} Nat instLENat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cv n) ce →
                            @LE.le.{0} Nat instLENat
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ce
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
                                work →
                              @LE.le.{0} Nat instLENat (ThreeSum.LightColorBands.space work W n g) lim.space →
                                @LE.le.{0} Int Int.instLEInt
                                    (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightColorBands.word W n g U))
                                    lim.word →
                                  @LE.le.{0} Nat instLENat
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                                        (ThreeSum.LightColorBands.depth W n g))
                                      lim.depth →
                                    Light.Seg μ src (@List.ofFn.{0} Int n x) →
                                      (∀ (i : Fin n),
                                          @LE.le.{0} Int Int.instLEInt
                                            (@abs.{0} Int instLatticeInt Int.instAddGroup (x i))
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
                                                            Fin
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                                (instOfNatNat (nat_lit 3))))
                                                          p))))
                                                  (@List.cons.{0} Int
                                                    (@Nat.cast.{0} Int instNatCastInt
                                                      (@Fin.val W
                                                        (@Prod.snd.{0, 0} (Fin W) (Fin W)
                                                          (@Prod.fst.{0, 0} (Prod.{0, 0} (Fin W) (Fin W))
                                                            (Prod.{0, 0} Bool Bool →
                                                              Fin
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                                  (instOfNatNat (nat_lit 3))))
                                                            p))))
                                                    (@List.cons.{0} Int
                                                      (@Nat.cast.{0} Int instNatCastInt
                                                        (@Fin.val
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                                          (@Prod.snd.{0, 0} (Prod.{0, 0} (Fin W) (Fin W))
                                                            (Prod.{0, 0} Bool Bool →
                                                              Fin
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                                  (instOfNatNat (nat_lit 3))))
                                                            p (@Prod.mk.{0, 0} Bool Bool Bool.false Bool.false))))
                                                      (@List.cons.{0} Int
                                                        (@Nat.cast.{0} Int instNatCastInt
                                                          (@Fin.val
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                              (instOfNatNat (nat_lit 3)))
                                                            (@Prod.snd.{0, 0} (Prod.{0, 0} (Fin W) (Fin W))
                                                              (Prod.{0, 0} Bool Bool →
                                                                Fin
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                                    (instOfNatNat (nat_lit 3))))
                                                              p (@Prod.mk.{0, 0} Bool Bool Bool.false Bool.true))))
                                                        (@List.cons.{0} Int
                                                          (@Nat.cast.{0} Int instNatCastInt
                                                            (@Fin.val
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                                (instOfNatNat (nat_lit 3)))
                                                              (@Prod.snd.{0, 0} (Prod.{0, 0} (Fin W) (Fin W))
                                                                (Prod.{0, 0} Bool Bool →
                                                                  Fin
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                                      (instOfNatNat (nat_lit 3))))
                                                                p (@Prod.mk.{0, 0} Bool Bool Bool.true Bool.false))))
                                                          (@List.cons.{0} Int
                                                            (@Nat.cast.{0} Int instNatCastInt
                                                              (@Fin.val
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                                  (instOfNatNat (nat_lit 3)))
                                                                (@Prod.snd.{0, 0} (Prod.{0, 0} (Fin W) (Fin W))
                                                                  (Prod.{0, 0} Bool Bool →
                                                                    Fin
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                                        (instOfNatNat (nat_lit 3))))
                                                                  p (@Prod.mk.{0, 0} Bool Bool Bool.true Bool.true))))
                                                            (@List.cons.{0} Int
                                                              (@Nat.cast.{0} Int instNatCastInt colors)
                                                              (@List.cons.{0} Int
                                                                (@Nat.cast.{0} Int instNatCastInt dst0)
                                                                (@List.cons.{0} Int
                                                                  (@Nat.cast.{0} Int instNatCastInt dst1)
                                                                  (@List.cons.{0} Int
                                                                    (@Nat.cast.{0} Int instNatCastInt dst2)
                                                                    (@List.cons.{0} Int
                                                                      (@Nat.cast.{0} Int instNatCastInt g)
                                                                      (@List.cons.{0} Int
                                                                        (@Nat.cast.{0} Int instNatCastInt av)
                                                                        (@List.cons.{0} Int
                                                                          (@Nat.cast.{0} Int instNatCastInt ae)
                                                                          (@List.cons.{0} Int
                                                                            (@Nat.cast.{0} Int instNatCastInt bv)
                                                                            (@List.cons.{0} Int
                                                                              (@Nat.cast.{0} Int instNatCastInt be)
                                                                              (@List.cons.{0} Int
                                                                                (@Nat.cast.{0} Int instNatCastInt cv)
                                                                                (@List.cons.{0} Int
                                                                                  (@Nat.cast.{0} Int instNatCastInt ce)
                                                                                  (@List.cons.{0} Int
                                                                                    (@Nat.cast.{0} Int instNatCastInt
                                                                                      work)
                                                                                    (@List.nil.{0}
                                                                                      Int))))))))))))))))))))))
                                          μ (ThreeSum.LightColorBands.time W n g) fun (r : Int) (ν : Nat → Int) =>
                                          And
                                            (ThreeSum.LightBandPreprocessing.Output ν av ae bv be cv ce work g hg
                                              (@ThreeSum.ColorClassLists.classList n W p x
                                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                                (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                              (@ThreeSum.ColorClassLists.classList n W p x
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                                (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                              (@ThreeSum.ColorClassLists.classList n W p x
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                (@Neg.neg.{0} Int Int.instNegInt
                                                  (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                                              r)
                                            (Light.Kept μ ν colors) := by
  exact @ThreeSum.LightColorBands.Procs.meets_sourceProof

#print axioms solution
