-- Prove2me | solution 1 for ThreeSum.LightBandPreprocessing.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:34:44.599529+00:00
-- url     : https://prove2.me/submissions/913df3c2-bf49-4d93-870b-5e81dbe17dc9

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
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
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
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
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
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_LightBandPreprocessing_Represents_keep
import Theorems.Thm_ThreeSum_LightHeaderBands_Procs_meets
import Theorems.Thm_ThreeSum_LightSortedBands_Prepared_transfer
import Theorems.Thm_ThreeSum_LightSortedBands_Procs_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
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





theorem size_le (n g : ℕ) : size n g ≤ n := by
  unfold size
  split_ifs with h
  · omega
  · have hdiv := Nat.div_le_self (n-1) g
    omega

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

theorem time_mono {a b c a' b' c' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    time a b c ≤ time a' b' c' := by
  have hw := width_mono ha hb hc
  have hlog := Nat.clog_mono_right 2 (show a+b+c+1 ≤ a'+b'+c'+1 by omega)
  unfold time clog2Time powTableTime LightBandTable.time LightBandTable.rowTime
    LightBandLookup.time LightBandLookup.searchTime
  gcongr

end ThreeSum.LightBandEnumeration

end

section


/-!
# Normalizing one color class and constructing all its band endpoints

This closed eleven-procedure program joins the actual merge sort, adjacent
deduplication, quotient computation, and endpoint passes. It writes the
distinct-value length and band count in a two-cell header. The following
cells are the lower endpoints and, after the distinct-value length, the
upper endpoints. The membership witness still refers to the original class.
-/

namespace ThreeSum.LightSortedBands

open Light ThreeSum.BandPartition

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

variable {lim : Limits} {P : Program}















































































































































/-- The constructed endpoint arrays directly instantiate the exact family
interface of the owner-listing machine. -/
theorem Prepared.family {μ : ℕ → ℤ} {values endpoints g : ℕ} {original : List ℤ}
    (h : Prepared μ values endpoints g original) (hg : 0 < g) :
    ∃ (L : List ℤ) (hs : L.Pairwise (· < ·)),
      Seg μ values L ∧ L.length ≤ original.length ∧ (∀ z, z ∈ L ↔ z ∈ original) ∧
      μ endpoints = (L.length : ℤ) ∧
      μ (endpoints+1) = (BandPartition.family (fun i => L.getD i 0) L.length g hg
        (getD_strict hs)).size ∧
      LightBandEnumeration.At μ (endpoints+2) (endpoints+2+L.length)
        (BandPartition.family (fun i => L.getD i 0) L.length g hg (getD_strict hs)) := by
  obtain ⟨L,hL,hs,hn,hmem,hlen,hcount,hlo,hhi⟩ := h
  exact ⟨L,hs,hL,hn,hmem,hlen,hcount,hlo,hhi⟩


































theorem family_bounded {L original : List ℤ} {g U : ℕ} (hg : 0 < g)
    (hs : L.Pairwise (· < ·)) (hmem : ∀ z, z ∈ L ↔ z ∈ original)
    (hU : ∀ z ∈ original, |z| ≤ (U : ℤ)) :
    LightBandEnumeration.Bounded
      (BandPartition.family (fun i => L.getD i 0) L.length g hg (getD_strict hs)) U := by
  have hget (i : ℕ) (hi : i < L.length) : |L.getD i 0| ≤ (U : ℤ) := by
    rw [List.getD_eq_getElem _ _ hi]
    exact hU _ ((hmem _).mp (List.getElem_mem hi))
  intro i hi
  exact ⟨hget _ (start_lt hg hi),hget _ (stop_sub_one_lt hg hi)⟩


















end ThreeSum.LightSortedBands

end

section


/-!
# Closed normalization and band listing for three supplied color classes

The three class arrays are sorted and deduplicated separately. Their actual
length/count headers then drive the actual owner-table enumerator. The program
has twenty fixed procedures. No sorting function, lookup function, or band
enumerator is supplied by the caller.
-/

namespace ThreeSum.LightBandPreprocessing

open Light ThreeSum.BandPartition

set_option maxHeartbeats 1800000
set_option maxRecDepth 5000

variable {lim : Limits} {P : Program}





































































theorem Procs.meets_sourceProof {pMain srcA srcB srcC av ae bv be cv ce work g U d : ℕ}
    {μ : ℕ → ℤ} {originalA originalB originalC : List ℤ} (R : Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hg : 0 < g)
    (hsrcAB : srcA+originalA.length ≤ srcB) (hsrcBC : srcB+originalB.length ≤ srcC)
    (hsrcCv : srcC+originalC.length ≤ av)
    (hav : av+originalA.length ≤ ae) (hae : ae+2+2*originalA.length ≤ bv)
    (hbv : bv+originalB.length ≤ be) (hbe : be+2+2*originalB.length ≤ cv)
    (hcv : cv+originalC.length ≤ ce) (hce : ce+2+2*originalC.length ≤ work)
    (hspace : space work originalA.length originalB.length originalC.length g ≤ lim.space)
    (hword : (word originalA.length originalB.length originalC.length g U : ℤ) ≤ lim.word)
    (hd : d+depth originalA.length originalB.length originalC.length g ≤ lim.depth)
    (hAread : Seg μ srcA originalA) (hBread : Seg μ srcB originalB) (hCread : Seg μ srcC originalC)
    (hAU : ∀ z ∈ originalA, |z| ≤ (U : ℤ)) (hBU : ∀ z ∈ originalB, |z| ≤ (U : ℤ))
    (hCU : ∀ z ∈ originalC, |z| ≤ (U : ℤ)) :
    Meets lim P pMain d
      [srcA,originalA.length,srcB,originalB.length,srcC,originalC.length,g,av,ae,bv,be,cv,ce,work]
      μ (time originalA.length originalB.length originalC.length g)
      (fun r μ' => Output μ' av ae bv be cv ce work g hg originalA originalB originalC r ∧
        Kept μ μ' srcA) := by
  have hspace' : work+(originalA.length+originalB.length+originalC.length)+
      LightBandEnumeration.count (size originalA.length g) (size originalB.length g) (size originalC.length g)+
      LightBandEnumeration.width (size originalA.length g) (size originalB.length g) (size originalC.length g)+1 ≤
      lim.space := hspace
  have hnormSpaceA : LightSortedBands.space work originalA.length ≤ lim.space := by
    unfold LightSortedBands.space; omega
  have hnormSpaceB : LightSortedBands.space work originalB.length ≤ lim.space := by
    unfold LightSortedBands.space; omega
  have hnormSpaceC : LightSortedBands.space work originalC.length ≤ lim.space := by
    unfold LightSortedBands.space; omega
  have hnormWord (n : ℕ) (hn : n ≤ originalA.length+originalB.length+originalC.length) :
      ((n+g+2 : ℕ) : ℤ) ≤ lim.word := by
    have hh : n+g+2 ≤ word originalA.length originalB.length originalC.length g U := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hnormDepth (n : ℕ) (hn : n ≤ originalA.length+originalB.length+originalC.length) :
      (d+1)+n+Nat.clog 2 n+3 ≤ lim.depth := by
    have hlog := Nat.clog_mono_right 2 hn
    unfold depth at hd
    omega
  have hgWord : ((g+2 : ℕ) : ℤ) ≤ lim.word := by simpa using hnormWord 0 (by omega)
  have hdSmall : d+4 ≤ lim.depth := by unfold depth at hd; omega
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
            ((R.prepare.meets (d := d + 1) (src := srcA) (values := av)
                (endpoints := ae) (work := work) hw hg (by omega) hav (by omega)
                hnormSpaceA (hnormWord _ (by omega)) (hnormDepth _ (by omega))
                hAread)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (R.prepare.meets (d := d + 1) (src := srcA) (values := av)
              (endpoints := ae) (work := work) hw hg (by omega) hav (by omega)
              hnormSpaceA (hnormWord _ (by omega)) (hnormDepth _ (by omega))
              hAread)
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightSortedBands.time, LightNormalize.time, sortTime,
                LightNormalize.dedupTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightSortedBands.time, LightNormalize.time, sortTime,
                LightNormalize.dedupTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, LightSortedBands.time,
                LightNormalize.time, sortTime, LightNormalize.dedupTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro aCount μ₁ ⟨haCount, hPreparedA, hkeep₁⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hBread₁ : Seg μ₁ srcB originalB := by
    intro i hi
    rw [hkeep₁ (srcB+i) (by omega) (by omega) (by omega) (by omega)]
    exact hBread i hi
  have hCread₁ : Seg μ₁ srcC originalC := by
    intro i hi
    rw [hkeep₁ (srcC+i) (by omega) (by omega) (by omega) (by omega)]
    exact hCread i hi
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
            ((R.prepare.meets (d := d + 1) (src := srcB) (values := bv)
                (endpoints := be) (work := work) hw hg (by omega) hbv (by omega)
                hnormSpaceB (hnormWord _ (by omega)) (hnormDepth _ (by omega))
                hBread₁)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (R.prepare.meets (d := d + 1) (src := srcB) (values := bv)
              (endpoints := be) (work := work) hw hg (by omega) hbv (by omega)
              hnormSpaceB (hnormWord _ (by omega)) (hnormDepth _ (by omega))
              hBread₁)
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightSortedBands.time, LightNormalize.time, sortTime,
                LightNormalize.dedupTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightSortedBands.time, LightNormalize.time, sortTime,
                LightNormalize.dedupTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, LightSortedBands.time,
                LightNormalize.time, sortTime, LightNormalize.dedupTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro bCount μ₂ ⟨hbCount, hPreparedB, hkeep₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hPreparedA₂ : LightSortedBands.Prepared μ₂ av ae g originalA := by
    apply hPreparedA.transfer
    intro a ha
    apply hkeep₂ a <;> rcases ha with ha | ha <;> omega
  have hCread₂ : Seg μ₂ srcC originalC := by
    intro i hi
    rw [hkeep₂ (srcC+i) (by omega) (by omega) (by omega) (by omega)]
    exact hCread₁ i hi
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
            ((R.prepare.meets (d := d + 1) (src := srcC) (values := cv)
                (endpoints := ce) (work := work) hw hg (by omega) hcv hce
                hnormSpaceC (hnormWord _ (by omega)) (hnormDepth _ (by omega))
                hCread₂)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (R.prepare.meets (d := d + 1) (src := srcC) (values := cv)
              (endpoints := ce) (work := work) hw hg (by omega) hcv hce
              hnormSpaceC (hnormWord _ (by omega)) (hnormDepth _ (by omega))
              hCread₂)
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightSortedBands.time, LightNormalize.time, sortTime,
                LightNormalize.dedupTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightSortedBands.time, LightNormalize.time, sortTime,
                LightNormalize.dedupTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, LightSortedBands.time,
                LightNormalize.time, sortTime, LightNormalize.dedupTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro cCount μ₃ ⟨hcCount, hPreparedC, hkeep₃⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hPreparedA₃ : LightSortedBands.Prepared μ₃ av ae g originalA := by
    apply hPreparedA₂.transfer
    intro a ha
    apply hkeep₃ a <;> rcases ha with ha | ha <;> omega
  have hPreparedB₃ : LightSortedBands.Prepared μ₃ bv be g originalB := by
    apply hPreparedB.transfer
    intro a ha
    apply hkeep₃ a <;> rcases ha with ha | ha <;> omega
  obtain ⟨A,hsA,hASeg,hALen,hAMem,hAHeader,hACount,hAAt⟩ := hPreparedA₃.family hg
  obtain ⟨B,hsB,hBSeg,hBLen,hBMem,hBHeader,hBCount,hBAt⟩ := hPreparedB₃.family hg
  obtain ⟨C,hsC,hCSeg,hCLen,hCMem,hCHeader,hCCount,hCAt⟩ := hPreparedC.family hg
  let aFamily := family (fun i => A.getD i 0) A.length g hg (LightSortedBands.getD_strict hsA)
  let bFamily := family (fun i => B.getD i 0) B.length g hg (LightSortedBands.getD_strict hsB)
  let cFamily := family (fun i => C.getD i 0) C.length g hg (LightSortedBands.getD_strict hsC)
  have hsa : aFamily.size ≤ size originalA.length g := size_mono hALen
  have hsb : bFamily.size ≤ size originalB.length g := size_mono hBLen
  have hsc : cFamily.size ≤ size originalC.length g := size_mono hCLen
  have hsan : aFamily.size ≤ originalA.length := hsa.trans (size_le _ _)
  have hsbn : bFamily.size ≤ originalB.length := hsb.trans (size_le _ _)
  have hscn : cFamily.size ≤ originalC.length := hsc.trans (size_le _ _)
  have hcountBound := LightBandEnumeration.count_mono hsa hsb hsc
  have hwidthBound := LightBandEnumeration.width_mono hsa hsb hsc
  have henumSpace : LightBandEnumeration.space work aFamily.size bFamily.size cFamily.size ≤ lim.space := by
    unfold LightBandEnumeration.space
    omega
  have henumWord : (LightBandEnumeration.word aFamily.size bFamily.size cFamily.size U : ℤ) ≤ lim.word := by
    have hh : LightBandEnumeration.word aFamily.size bFamily.size cFamily.size U ≤
        word originalA.length originalB.length originalC.length g U := by
      unfold word LightBandEnumeration.word
      omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have henumDepth : (d+1)+LightBandEnumeration.width aFamily.size bFamily.size cFamily.size+5 ≤ lim.depth := by
    unfold depth at hd
    omega
  have henumTime : LightHeaderBands.time aFamily.size bFamily.size cFamily.size ≤
      LightHeaderBands.time (size originalA.length g) (size originalB.length g) (size originalC.length g) :=
    Nat.add_le_add_right (LightBandEnumeration.time_mono hsa hsb hsc) 100
  have hrepA : Represents μ₃ av ae g hg originalA A hsA :=
    ⟨hASeg,hALen,hAMem,hAHeader,hACount,hAAt⟩
  have hrepB : Represents μ₃ bv be g hg originalB B hsB :=
    ⟨hBSeg,hBLen,hBMem,hBHeader,hBCount,hBAt⟩
  have hrepC : Represents μ₃ cv ce g hg originalC C hsC :=
    ⟨hCSeg,hCLen,hCMem,hCHeader,hCCount,hCAt⟩
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
            (((R.enumerate.meets (d := d + 1) aFamily bFamily cFamily hw
                    (by omega) (by omega) (by omega) henumSpace henumWord
                    henumDepth hrepA.2.2.2 hrepB.2.2.2 hrepC.2.2.2
                    (LightSortedBands.family_bounded hg hsA hAMem hAU)
                    (LightSortedBands.family_bounded hg hsB hBMem hBU)
                    (LightSortedBands.family_bounded hg hsC hCMem hCU)).mono_time
                henumTime)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            ((R.enumerate.meets (d := d + 1) aFamily bFamily cFamily hw (by omega)
                  (by omega) (by omega) henumSpace henumWord henumDepth
                  hrepA.2.2.2 hrepB.2.2.2 hrepC.2.2.2
                  (LightSortedBands.family_bounded hg hsA hAMem hAU)
                  (LightSortedBands.family_bounded hg hsB hBMem hBU)
                  (LightSortedBands.family_bounded hg hsC hCMem hCU)).mono_time
              henumTime)
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightSortedBands.time, LightNormalize.time, sortTime,
                LightNormalize.dedupTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightSortedBands.time, LightNormalize.time, sortTime,
                LightNormalize.dedupTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, LightSortedBands.time,
                LightNormalize.time, sortTime, LightNormalize.dedupTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro result μ₄ ⟨hresult, htable, hkeep₄⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  refine ⟨⟨A,hsA,B,hsB,C,hsC,hresult,
    hrepA.keep hkeep₄ (by omega) (by omega),
    hrepB.keep hkeep₄ (by omega) (by omega),
    hrepC.keep hkeep₄ (by omega) hce,htable⟩,?_⟩
  intro a ha
  change μ₄ a = μ a
  rw [hkeep₄ a (by omega),hkeep₃ a (by omega) (by omega) (by omega) (by omega),
    hkeep₂ a (by omega) (by omega) (by omega) (by omega),
    hkeep₁ a (by omega) (by omega) (by omega) (by omega)]







































end ThreeSum.LightBandPreprocessing

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {pMain srcA srcB srcC av ae bv be cv ce work g U d : Nat} {μ : Nat → Int}
  {originalA originalB originalC : List.{0} Int} (R : ThreeSum.LightBandPreprocessing.Procs P pMain),
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    ∀ (hg : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) g),
      @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcA (@List.length.{0} Int originalA)) srcB →
        @LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcB (@List.length.{0} Int originalB))
            srcC →
          @LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcC (@List.length.{0} Int originalC))
              av →
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) av (@List.length.{0} Int originalA))
                ae →
              @LE.le.{0} Nat instLENat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ae
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.length.{0} Int originalA)))
                  bv →
                @LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bv
                      (@List.length.{0} Int originalB))
                    be →
                  @LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) be
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          (@List.length.{0} Int originalB)))
                      cv →
                    @LE.le.{0} Nat instLENat
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cv
                          (@List.length.{0} Int originalC))
                        ce →
                      @LE.le.{0} Nat instLENat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ce
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              (@List.length.{0} Int originalC)))
                          work →
                        @LE.le.{0} Nat instLENat
                            (ThreeSum.LightBandPreprocessing.space work (@List.length.{0} Int originalA)
                              (@List.length.{0} Int originalB) (@List.length.{0} Int originalC) g)
                            lim.space →
                          @LE.le.{0} Int Int.instLEInt
                              (@Nat.cast.{0} Int instNatCastInt
                                (ThreeSum.LightBandPreprocessing.word (@List.length.{0} Int originalA)
                                  (@List.length.{0} Int originalB) (@List.length.{0} Int originalC) g U))
                              lim.word →
                            @LE.le.{0} Nat instLENat
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                                  (ThreeSum.LightBandPreprocessing.depth (@List.length.{0} Int originalA)
                                    (@List.length.{0} Int originalB) (@List.length.{0} Int originalC) g))
                                lim.depth →
                              Light.Seg μ srcA originalA →
                                Light.Seg μ srcB originalB →
                                  Light.Seg μ srcC originalC →
                                    (∀ (z : Int),
                                        @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int)
                                            originalA z →
                                          @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup z)
                                            (@Nat.cast.{0} Int instNatCastInt U)) →
                                      (∀ (z : Int),
                                          @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int)
                                              originalB z →
                                            @LE.le.{0} Int Int.instLEInt
                                              (@abs.{0} Int instLatticeInt Int.instAddGroup z)
                                              (@Nat.cast.{0} Int instNatCastInt U)) →
                                        (∀ (z : Int),
                                            @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int)
                                                originalC z →
                                              @LE.le.{0} Int Int.instLEInt
                                                (@abs.{0} Int instLatticeInt Int.instAddGroup z)
                                                (@Nat.cast.{0} Int instNatCastInt U)) →
                                          Light.Meets lim P pMain d
                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcA)
                                              (@List.cons.{0} Int
                                                (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int originalA))
                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcB)
                                                  (@List.cons.{0} Int
                                                    (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int originalB))
                                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcC)
                                                      (@List.cons.{0} Int
                                                        (@Nat.cast.{0} Int instNatCastInt
                                                          (@List.length.{0} Int originalC))
                                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt g)
                                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt av)
                                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt ae)
                                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt bv)
                                                                (@List.cons.{0} Int
                                                                  (@Nat.cast.{0} Int instNatCastInt be)
                                                                  (@List.cons.{0} Int
                                                                    (@Nat.cast.{0} Int instNatCastInt cv)
                                                                    (@List.cons.{0} Int
                                                                      (@Nat.cast.{0} Int instNatCastInt ce)
                                                                      (@List.cons.{0} Int
                                                                        (@Nat.cast.{0} Int instNatCastInt work)
                                                                        (@List.nil.{0} Int)))))))))))))))
                                            μ
                                            (ThreeSum.LightBandPreprocessing.time (@List.length.{0} Int originalA)
                                              (@List.length.{0} Int originalB) (@List.length.{0} Int originalC) g)
                                            fun (r : Int) (μ' : Nat → Int) =>
                                            And
                                              (ThreeSum.LightBandPreprocessing.Output μ' av ae bv be cv ce work g hg
                                                originalA originalB originalC r)
                                              (Light.Kept μ μ' srcA) := by
  exact @ThreeSum.LightBandPreprocessing.Procs.meets_sourceProof

#print axioms solution
