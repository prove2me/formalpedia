-- Prove2me | solution 1 for ThreeSum.LightBoxStages.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:41:48.625975+00:00
-- url     : https://prove2.me/submissions/566b43e6-89aa-4893-a027-1d7c939252de

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
import Definitions.Def_ThreeSum1962Source_Bundle10
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
import Mathlib.Data.Finset.Max
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
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_Light_Ends_for
import Theorems.Thm_ThreeSum_BoxStages_stageValue_abs_le
import Theorems.Thm_ThreeSum_LightDownsetSize_meets
import Theorems.Thm_ThreeSum_LightZetaPass_meets
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt
import Theorems.Thm_ThreeSum_Subset_partialZeta_insert


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BoxStages
end ThreeSum.BoxStages
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
# Exact subset identities used by the proposed 3SUM algorithm

This module proves the algebraic identities, rather than taking the claimed
algorithm or its running time as an assumption.  `zeta` is the ordinary finite
subset sum; `mobius` is its signed inverse.  The fixed-cardinality specialization
is the identity used by the repeated histogram construction.
-/

namespace ThreeSum.Subset

open scoped BigOperators

variable {α : Type*} [DecidableEq α]































































































































































































































































/-! ## Stored partial zeta stages -/










theorem partialZeta_empty (f : Finset α → ℤ) (u : Finset α) :
    partialZeta ∅ f u = f u := by
  simp [partialZeta]


















































































































































































/-! ## Prefix reporting mass -/




























































end ThreeSum.Subset

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
# Canonical sparse boxes as stored prefix-zeta stages

A global coordinate prefix intersects each flagged set in an initial
segment. Storing those initialCoords stages uses only a polynomial factor more
than the compact downset. The resulting entries are exactly the signed
box sums used by the sparse-query partition.
-/

namespace ThreeSum.BoxStages

open Finset



@[simp] theorem mem_prefix {L j : ℕ} (a : Fin L) : a ∈ initialCoords L j ↔ a.val < j := by
  simp [initialCoords]

@[simp] theorem prefix_zero (L : ℕ) : initialCoords L 0 = ∅ := by
  ext a
  simp








theorem nextCoord_not_mem {L j : ℕ} (hj : j < L) : nextCoord j hj ∉ initialCoords L j := by
  simp [nextCoord]

theorem prefix_succ {L j : ℕ} (hj : j < L) :
    initialCoords L (j+1) = insert (nextCoord j hj) (initialCoords L j) := by
  ext a
  simp only [mem_prefix,Finset.mem_insert,Fin.ext_iff,nextCoord]
  omega




@[simp] theorem stageValue_zero {L : ℕ} (f : Finset (Fin L) → ℤ) : stageValue f 0 = f := by
  funext S
  simp [stageValue,Subset.partialZeta_empty]

theorem stageValue_succ {L j : ℕ} (f : Finset (Fin L) → ℤ) (hj : j < L) :
    stageValue f (j+1) = Subset.zetaStep (nextCoord j hj) (stageValue f j) := by
  funext S
  rw [stageValue,prefix_succ hj]
  exact Subset.partialZeta_insert f S (initialCoords L j) (nextCoord j hj) (nextCoord_not_mem hj)



































































































end ThreeSum.BoxStages

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
# Building and retaining every compact prefix-zeta stage

The fixed program computes the compact table stride, then makes one
coordinate pass per bit. All earlier stages remain available for canonical
sparse-box queries. Its workspace is `(L+2)*downsetCap + O(L^2)`, and its
time is a polynomial in `L` times `downsetCap`. Intermediate word bounds
are derived from the original table values.
-/

namespace ThreeSum.LightBoxStages

open Light ThreeSum.SubsetAddress ThreeSum.BoxStages ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}



























theorem meets_sourceProof
    {pMain pSize pPass pEnumSetup pEnum pBatch pCell pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ}
    (hmain : P[pMain]? = some (body pSize pPass))
    (hSize : P[pSize]? = some (LightDownsetSize.body pSetup pOffset))
    (hPass : P[pPass]? = some (LightZetaPass.body pEnumSetup pBatch))
    (hEnumSetup : P[pEnumSetup]? = some (LightSubsetEnumerationSetup.body pPowers pEnum))
    (hEnum : P[pEnum]? = some (LightSubsetEnumeration.body pEnum))
    (hBatch : P[pBatch]? = some (LightZetaBatch.body pCell))
    (hCell : P[pCell]? = some (LightZetaCell.body pSetup pOffset pErase pRank))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body)
    (hErase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L cut base maskBase work U d : ℕ}
    (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hdata : base+(L+1)*downsetCap L cut ≤ maskBase)
    (hmasks : maskBase+downsetCap L cut ≤ work)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^L*U : ℕ) : ℤ) ≤ lim.word)
    (hread : TableAt μ base cut f) (hvalues : ∀ T, T.card ≤ cut → |f T| ≤ U)
    (hd : d+L+7 ≤ lim.depth) :
    Meets lim P pMain d [L,cut,base,maskBase,work] μ (time L cut)
      (fun _ μ' => StoredThrough μ' base cut f L ∧
        KeptBut μ μ' maskBase base ((L+1)*downsetCap L cut)) := by
  have hstage (i : ℕ) (hi : i ≤ L) :
      stageBase base (downsetCap L cut) i+downsetCap L cut ≤ maskBase := by
    have hm := Nat.mul_le_mul_right (downsetCap L cut) (Nat.succ_le_succ hi)
    unfold stageBase
    simp only [Nat.succ_mul,Nat.add_mul,Nat.one_mul] at hm hdata
    omega
  have hfirst := hstage 0 (by omega)
  simp only [stageBase,Nat.zero_mul,Nat.add_zero] at hfirst
  apply Meets.of_body hmain
  unfold body time
  have hs := LightDownsetSize.meets (d := d+1) (μ := μ)
    hSize C hOffset hw hspace hword hcut (by omega)
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
      | refine Light.Ends.callToThen (hs _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hs ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightDownsetSize.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightDownsetSize.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, LightDownsetSize.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro cap μ₁ ⟨hcap, hsizeKept⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  subst cap
  refine Ends.for (Inv μ cut base maskBase work f) L
    (LightZetaPass.time L cut+50) ?start ?round ?done ?bound
    (hT := by first
              |
                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                      LightDownsetSize.time]);
                  (first
                    | omega
                    | ((ring_nf); (omega))))
              | omega
              |
                (simp [LightDownsetSize.time] <;>
                    first
                    | omega
                    | ((ring_nf); (omega))))
  case start =>
    refine ⟨0,μ₁,?_,?_,?_⟩
    · simp [update_frame_setLocal]
      change frame [(L : ℤ),cut,base,maskBase,work,downsetCap L cut,0] =
        frame ([(L : ℤ),cut,base,maskBase,work,downsetCap L cut,0] ++ [0])
      exact (frame_append_zeros _ 1).symm
    · intro i hi
      have he : i = 0 := by omega
      subst i
      intro S hS
      have hr := subsetRank_lt hS
      simpa only [stageBase,Nat.zero_mul,Nat.add_zero,stageValue_zero] using
        (hsizeKept _ (by omega)).trans (hread S hS)
    · intro i hi
      exact hsizeKept i (by omega)
  case round =>
    rintro j _ hj _ ⟨r,μ',rfl,hstored,hkept⟩
    have hsource := hstored j le_rfl
    have hsrc := hstage j (by omega)
    have hdst := hstage (j+1) (by omega)
    have hsep : Apart (stageBase base (downsetCap L cut) j) (downsetCap L cut)
        (stageBase base (downsetCap L cut) (j+1)) (downsetCap L cut) := by
      left
      simp [stageBase,Nat.add_mul,Nat.add_assoc]
    have hcurrentValues := stageValue_abs_le f hvalues j (Nat.le_of_lt hj)
    have hvalue : 2*(((2^j*U : ℕ) : ℤ)) ≤ lim.word := by
      have hp : (2^(j+1) : ℕ) ≤ 2^L := Nat.pow_le_pow_right (by decide) (by omega)
      have hu := Nat.mul_le_mul_right U hp
      have he : 2*(2^j*U) = 2^(j+1)*U := by rw [pow_succ]; ring
      have hh : (2*(2^j*U) : ℕ) ≤ 2^L*U := by rw [he]; exact hu
      exact (by exact_mod_cast hh : 2*(((2^j*U : ℕ) : ℤ)) ≤ ((2^L*U : ℕ) : ℤ)).trans hvalueWord
    have hc := LightZetaPass.meets (d := d+1) hPass hEnumSetup hEnum hBatch hCell
      C hOffset hErase (nextCoord j hj) (stageValue f j)
      hw hcut hsrc hdst hmasks hsep hspace hword hvalue hsource hcurrentValues (by omega)
    have hsrcCast : (base : ℤ)+(j : ℤ)*(downsetCap L cut : ℤ) =
        (stageBase base (downsetCap L cut) j : ℤ) := by
      simp [stageBase]
    have hdstCast : (base : ℤ)+((j : ℤ)+1)*(downsetCap L cut : ℤ) =
        (stageBase base (downsetCap L cut) (j+1) : ℤ) := by
      simp [stageBase]
    unfold roundBody
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
                  nextCoord, hsrcCast, hdstCast]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [nextCoord, hsrcCast, hdstCast] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 => omega);
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, nextCoord, hsrcCast,
                  hdstCast] <;>
                omega)));
      (on_goal -1 =>
          ((rintro res μ₂ ⟨hnew, hpassKept⟩);
            (try with_unfolding_none refine Light.Ends.skip ?_)))
    refine ⟨by simp,res,μ₂,?_,?_,?_⟩
    · simp [update_frame_setLocal]
    · intro i hi
      by_cases heq : i = j+1
      · subst i
        simpa only [stageValue_succ f hj] using hnew
      · have hij : i ≤ j := by omega
        have himul := Nat.mul_le_mul_right (downsetCap L cut) hij
        intro S hS
        have hr := subsetRank_lt hS
        have hbefore : stageBase base (downsetCap L cut) i+subsetRank S <
            stageBase base (downsetCap L cut) (j+1) := by
          unfold stageBase
          simp only [Nat.add_mul,Nat.one_mul]
          omega
        have hiend := hstage i (by omega)
        exact (hpassKept _ ⟨by omega,Or.inl hbefore⟩).trans (hstored i hij S hS)
    · intro i hi
      have hnextLow : base ≤ stageBase base (downsetCap L cut) (j+1) := by
        unfold stageBase
        omega
      have hnextHigh := hstage (j+1) (by omega)
      have hmul := Nat.mul_le_mul_right (downsetCap L cut) (show j+2 ≤ L+1 by omega)
      have hnextEnd : stageBase base (downsetCap L cut) (j+1)+downsetCap L cut ≤
          base+(L+1)*downsetCap L cut := by
        unfold stageBase
        simp only [Nat.add_mul,Nat.one_mul] at hmul ⊢
        omega
      exact (hpassKept i ⟨hi.1,by omega⟩).trans (hkept i hi)
  case done =>
    rintro _ _ ⟨r,μ',rfl,hstored,hkept⟩
    exact ⟨hstored,hkept⟩
  case bound =>
    rintro j _ hj _ ⟨r,μ',rfl,_,_⟩
    (((try have := Light.Std.space_le (by assumption)));
      ((try have := Light.Std.const_le (by assumption)));
      (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))





































































end ThreeSum.LightBoxStages

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program}
  {pMain pSize pPass pEnumSetup pEnum pBatch pCell pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : Nat},
  @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMain)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightBoxStages.body pSize pPass)) →
    @Eq.{1} (Option.{0} Light.Stmt)
        (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
          (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
          (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pSize)
        (@Option.some.{0} Light.Stmt (ThreeSum.LightDownsetSize.body pSetup pOffset)) →
      @Eq.{1} (Option.{0} Light.Stmt)
          (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
            (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
            (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pPass)
          (@Option.some.{0} Light.Stmt (ThreeSum.LightZetaPass.body pEnumSetup pBatch)) →
        @Eq.{1} (Option.{0} Light.Stmt)
            (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
              (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
              (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pEnumSetup)
            (@Option.some.{0} Light.Stmt (ThreeSum.LightSubsetEnumerationSetup.body pPowers pEnum)) →
          @Eq.{1} (Option.{0} Light.Stmt)
              (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
                (fun (as : List.{0} Light.Stmt) (i : Nat) =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
                (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pEnum)
              (@Option.some.{0} Light.Stmt (ThreeSum.LightSubsetEnumeration.body pEnum)) →
            @Eq.{1} (Option.{0} Light.Stmt)
                (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
                  (fun (as : List.{0} Light.Stmt) (i : Nat) =>
                    @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
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
                      ∀ {μ : Nat → Int} {L cut base maskBase work U d : Nat} (f : Finset.{0} (Fin L) → Int),
                        @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
                          @LE.le.{0} Nat instLENat cut L →
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
                                        (@Nat.cast.{0} Int instNatCastInt
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)
                                            U))
                                        lim.word →
                                      @ThreeSum.LightZetaCell.TableAt L μ base cut f →
                                        (∀ (T : Finset.{0} (Fin L)),
                                            @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin L) T) cut →
                                              @LE.le.{0} Int Int.instLEInt
                                                (@abs.{0} Int instLatticeInt Int.instAddGroup (f T))
                                                (@Nat.cast.{0} Int instNatCastInt U)) →
                                          @LE.le.{0} Nat instLENat
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d L)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                              lim.depth →
                                            Light.Meets lim P pMain d
                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cut)
                                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt base)
                                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt maskBase)
                                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                                        (@List.nil.{0} Int))))))
                                              μ (ThreeSum.LightBoxStages.time L cut) fun (x : Int) (μ' : Nat → Int) =>
                                              And (@ThreeSum.LightBoxStages.StoredThrough L μ' base cut f L)
                                                (Light.KeptBut μ μ' maskBase base
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) L
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                    (ThreeSum.SubsetAddress.downsetCap L cut))) := by
  exact @ThreeSum.LightBoxStages.meets_sourceProof

#print axioms solution
