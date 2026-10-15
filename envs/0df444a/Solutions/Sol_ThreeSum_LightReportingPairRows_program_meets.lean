-- Prove2me | solution 1 for ThreeSum.LightReportingPairRows.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:25:55.049998+00:00
-- url     : https://prove2.me/submissions/473fca51-bbb1-4ace-831d-c220645eb44b

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
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
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
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
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
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
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
import Theorems.Thm_Light_Ends_for
import Theorems.Thm_Light_Ends_pass
import Theorems.Thm_ThreeSum_LightQueryEnumeration_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_meets
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_union_sdiff
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_leftAt_card
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_lefts_length
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_rights_length


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LayerCounts
end ThreeSum.LayerCounts
namespace ThreeSum.LightArray
end ThreeSum.LightArray
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.ReportingHostPairEnumeration
end ThreeSum.ReportingHostPairEnumeration
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# Exact counts for the local subset graph

These are counts of the executable finite sets used by the graph, rather
than abstract numerical cardinality hypotheses.  An edge is an ordered
pair of disjoint `h`-subsets of `Fin L`.
-/

namespace ThreeSum.LayerCounts

open Finset


























































































theorem vertex_degree_identity (L h : ℕ) :
    L.choose h * (L - h).choose h = L.choose (2 * h) * (2 * h).choose h := by
  simpa [show 2 * h - h = h by omega] using
    (Nat.choose_mul (n := L) (k := 2 * h) (s := h) (by omega)).symm

















end ThreeSum.LayerCounts

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












/-- The natural number behind an address that is a sum of two natural numbers. -/
@[simp] theorem toNat_natCast_add_natCast (a b : ℕ) : ((a : ℤ) + (b : ℤ)).toNat = a + b := by
  rw [← Nat.cast_add, Int.toNat_natCast]

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

/-- A piece of the program about which `h` is known, followed by the rest of the program, which gets
the steps that are left. -/
theorem Ends.pieceThen {σ : State} {T T₁ : ℕ} {s₁ s₂ : Stmt} {R Q : State → Prop}
    (h : Ends lim P d s₁ σ T₁ R) (rest : ∀ σ', R σ' → Ends lim P d s₂ σ' (T - T₁) Q)
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
  Ends.next T₁ (h.mono le_rfl rest) hT





































































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

/-- A cell that has not been written (yet). -/
theorem wrote_rest {a : ℕ} (h : Outside dst j a) : wrote μ dst f j a = μ a := by
  unfold wrote
  rw [if_neg (by omega)]


























/-! ## The tactics -/









































end Light

end
end

section


/-!
# Costed array arithmetic in the benchmark's imperative language

These are actual `Light.Stmt` programs and `Light.Meets` execution proofs.
Their contracts count every expression evaluation and memory operation.
-/

namespace ThreeSum.LightArray

open Light

variable {lim : Limits} {P : Program} {d : ℕ}





theorem source_read {μ : ℕ → ℤ} {src dst n j : ℕ} {f : ℕ → ℤ}
    (h : SourceSafe src dst n) (hj : j < n) :
    wrote μ dst f j (src + j) = μ (src + j) := by
  rcases h with rfl | h
  · exact wrote_rest (by omega)
  · exact wrote_rest (by omega)
































































end ThreeSum.LightArray

end

section


/-! # Costed affine scans used to form reporting child-prefix masks -/

namespace ThreeSum.LightReportingAffine

open Light ThreeSum.LightArray

variable {lim : Limits} {P : Program} {d : ℕ}






theorem meets {p src dst n : ℕ} {b c : ℤ} {μ : ℕ → ℤ}
    (hp : P[p]? = some body)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+n ≤ lim.space) (hdst : dst+n ≤ lim.space)
    (hsep : SourceSafe src dst n)
    (hmul : ∀ i < n, |c*μ (src+i)| ≤ lim.word)
    (hsum : ∀ i < n, |b+c*μ (src+i)| ≤ lim.word) :
    Meets lim P p d [src,dst,n,b,c] μ (time n)
      (fun _ μ' => (∀ i < n, μ' (dst+i) = b+c*μ (src+i)) ∧ SameOutside μ μ' dst n) := by
  refine .of_body hp (Ends.pass (fun i => b+c*μ (src+i))
    (fun i hi => ?_) ⟨fun i hi => wrote_done (f := fun i => b+c*μ (src+i)) hi,
      by ((try refine Light.SameOn.cell ?_); (intro apspMacro_27193_0 apspMacro_27193_1);
           (first
             |
               ((((repeat
                         (((with_reducible
                                 rename Light.SameOn _ _ _ => apspMacro_27193_2));
                           ((try
                                 have :=
                                   apspMacro_27193_2 apspMacro_27193_0 (by omega)));
                           (revert apspMacro_27193_2)));
                     (intros);
                     (try simp only [Function.update_apply, Light.wrote] at *)));
                 (omega))
             |
               ((simp [] at apspMacro_27193_1);
                 (((repeat
                         (((with_reducible
                                 rename Light.SameOn _ _ _ => apspMacro_27193_3));
                           ((try
                                 have :=
                                   apspMacro_27193_3 apspMacro_27193_0 (by omega)));
                           (revert apspMacro_27193_3)));
                     (intros);
                     (try simp only [Function.update_apply, Light.wrote] at *)));
                 (omega))
             |
               ((((repeat
                         (((with_reducible
                                 rename Light.SameOn _ _ _ => apspMacro_27193_4));
                           ((try
                                 have :=
                                   apspMacro_27193_4 apspMacro_27193_0 (by omega)));
                           (revert apspMacro_27193_4)));
                     (intros);
                     (try simp only [Function.update_apply, Light.wrote] at *)));
                 (fail
                     "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                               SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                               its condition K x does not follow from the hypotheses."))))⟩ hw hdst rfl rfl (hT := by first
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
                                                                                                                              | ((ring_nf); (omega)))))
  have hr := source_read (μ := μ) (f := fun i => b+c*μ (src+i)) hsep hi
  have hm := abs_le.mp (hmul i hi)
  have hs := abs_le.mp (hsum i hi)
  (((try have := Light.Std.space_le (by assumption)));
    ((try have := Light.Std.const_le (by assumption)));
    (simp [Light.Limits.Addr, abs_le, -abs_mul, hr] <;> omega))













end ThreeSum.LightReportingAffine

end

section


/-! # Exact arithmetic subtraction of one subset mask from another -/

namespace ThreeSum.MaskDifference

open Finset ThreeSum.SubsetAddress

theorem subsetMask_sum {L : ℕ} (S : Finset (Fin L)) :
    subsetMask S = ∑ i ∈ S, 2^i.val := by
  simp [subsetMask,maskOf,natPositions]







































theorem subsetMask_sdiff_int {L : ℕ} (Q U : Finset (Fin L)) (hU : U ⊆ Q) :
    (subsetMask Q : ℤ)-(subsetMask U : ℤ) = (subsetMask (Q \ U) : ℤ) := by
  have h := subsetMask_union_sdiff Q U hU
  have hz : (subsetMask U : ℤ)+(subsetMask (Q \ U) : ℤ) = (subsetMask Q : ℤ) := by
    exact_mod_cast h
  omega

end ThreeSum.MaskDifference

end

section


/-!
# A direct ordered enumeration of every local balanced row pair

First enumerate the h-subsets, then enumerate h-subsets of each complement.
The list contains every edge exactly once and has the exact local catalog
size, without scanning the ambient Boolean cube or all pairs of vertices.
-/

namespace ThreeSum.ReportingHostPairEnumeration

open Finset ThreeSum.SubsetAddress LayerCounts LocalGraph

set_option linter.unusedSimpArgs false



























theorem lefts_masks (L h : ℕ) : (lefts L h).map subsetMask = enumerateLayer L h := by
  apply List.ext_getElem
  · simp [lefts]
  · intro i hi hi'
    simp only [List.getElem_map,lefts,List.getElem_map]
    exact MaskDecode.subsetMask_decode ((mem_enumerateLayer L h _).mp (List.getElem_mem hi')).1































































theorem leftAt_eq_get {L h i : ℕ} (hi : i < L.choose h) :
    leftAt L h i = (lefts L h)[i]'(by simpa using hi) := by
  simp [leftAt,List.getElem?_eq_getElem,hi]





theorem rightAt_eq_get {L h i j : ℕ} (hi : i < L.choose h) (hj : j < (L-h).choose h) :
    rightAt L h i j = (rights (leftAt L h i) h)[j]'(by rw [rights_length _ (leftAt_card hi)]; exact hj) := by
  have hlen : j < (rights (leftAt L h i) h).length := by rw [rights_length _ (leftAt_card hi)]; exact hj
  simp [rightAt,List.getElem?_eq_getElem hlen]








theorem subsetMask_univ_succ (L : ℕ) : subsetMask (Finset.univ : Finset (Fin L))+1 = 2^L := by
  rw [MaskDifference.subsetMask_sum,Fin.sum_univ_eq_sum_range]
  induction L with
  | zero => simp
  | succ L ih =>
      rw [Finset.sum_range_succ,Nat.pow_succ]
      omega

theorem leftAt_mask {L h i : ℕ} (hi : i < L.choose h) :
    subsetMask (leftAt L h i) = (enumerateLayer L h)[i]'(by rw [enumerateLayer_length]; exact hi) := by
  have hiL : i < (lefts L h).length := by rw [lefts_length]; exact hi
  have hiE : i < (enumerateLayer L h).length := by rw [enumerateLayer_length]; exact hi
  have he := congrArg (fun xs : List ℕ => xs[i]?.getD 0) (lefts_masks L h)
  rw [leftAt_eq_get hi]
  simpa only [List.getElem?_map,List.getElem?_eq_getElem hiL,
    List.getElem?_eq_getElem hiE,Option.map_some,Option.getD_some] using he

end ThreeSum.ReportingHostPairEnumeration

end

section


/-!
# Actual direct construction of all local balanced row pairs

An own-power layer enumerator constructs the left subsets. For each left
subset, an actual output-sensitive query enumerator constructs its disjoint
right subsets, and an affine pass writes the matching repeated left mask.
-/

namespace ThreeSum.LightReportingPairRows

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostPairEnumeration

set_option maxHeartbeats 1800000

variable {lim : Limits}


































theorem program_meets_sourceProof {μ : ℕ → ℤ} {L h srcS dstL dstR work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hh : 2*h ≤ L)
    (hS : srcS+L.choose h ≤ dstL)
    (hL : dstL+L.choose h*(L-h).choose h ≤ dstR)
    (hR : dstR+L.choose h*(L-h).choose h ≤ work)
    (hspace : work+2*L+2 ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+L+3 ≤ lim.depth) :
    Meets lim program 7 d [L,h,srcS,dstL,dstR,work] μ (time L h)
      (fun r μ' => r = (L.choose (2*h)*(2*h).choose h : ℤ) ∧
        SegN μ' srcS (enumerateLayer L h) ∧
        (∀ i < L.choose h, ∀ j < (L-h).choose h,
          μ' (dstL+i*(L-h).choose h+j) = (subsetMask (leftAt L h i) : ℤ) ∧
          μ' (dstR+i*(L-h).choose h+j) = (subsetMask (rightAt L h i j) : ℤ)) ∧
        Kept μ μ' srcS) := by
  have hdeg : 0 < (L-h).choose h := Nat.choose_pos (by omega)
  have hverts : 0 < L.choose h := Nat.choose_pos (by omega)
  have hmask (S : Finset (Fin L)) : (subsetMask S : ℤ) ≤ lim.word := by
    have hb : subsetMask S ≤ 2^(L+1) := (Nat.le_of_lt (subsetMask_isMask S).1).trans
      (Nat.pow_le_pow_right (by decide) (by omega))
    exact (Int.ofNat_le.mpr hb).trans hword
  have hfullWord := hmask (Finset.univ : Finset (Fin L))
  apply Meets.of_body (p := 7) (by rfl : program[7]? = some (body 5 0 6))
  unfold body time
  have hs := LightSubsetEnumerationSetup.meets (P := program) (pMain := 5) (pPowers := 2)
    (pEnum := 4) (d := d+1) (μ := μ) (L := L) (k := h) (dst := srcS) (work := work)
    rfl rfl rfl hw (by omega) hword (by omega) (by omega) (by omega)
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
                LightSubsetEnumerationSetup.time, roundTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightSubsetEnumerationSetup.time, roundTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul,
                LightSubsetEnumerationSetup.time, roundTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro len μ₁ ⟨hlen, hlefts, hpowers, hkeepLayer⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  subst len
  have hpow := hpowers L le_rfl
  have hpowNat : μ₁ (work+L) = ((2^L : ℕ) : ℤ) := by simpa using hpow
  have hfull : ((2^L : ℕ) : ℤ)-1 = (subsetMask (Finset.univ : Finset (Fin L)) : ℤ) := by
    have he : (subsetMask (Finset.univ : Finset (Fin L)) : ℤ)+1 = ((2^L : ℕ) : ℤ) := by
      exact_mod_cast subsetMask_univ_succ L
    omega
  have hfullInt : (2 : ℤ)^L-1 = (subsetMask (Finset.univ : Finset (Fin L)) : ℤ) := by simpa using hfull
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine
        Light.Ends.setToThen (subsetMask (Finset.univ : Finset (Fin L)) : ℕ) ?_ ?_
          ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hpow,
                hpowNat, hfull, hfullInt, LightSubsetEnumerationSetup.time,
                roundTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hpow, hpowNat, hfull, hfullInt, LightSubsetEnumerationSetup.time,
                roundTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hpow, hpowNat, hfull,
                hfullInt, LightSubsetEnumerationSetup.time, roundTime] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightSubsetEnumerationSetup.time, roundTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightSubsetEnumerationSetup.time, roundTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul,
                LightSubsetEnumerationSetup.time, roundTime] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  refine Ends.pieceThen (Ends.for (lim := lim) (P := program) (d := d) (i := 9) (hi := v 6)
    (body := roundBody 0 6) (T := L.choose h*(roundTime L h+20)+70)
    (Q := Inv μ L h srcS dstL dstR work (L.choose h))
    (Inv μ L h srcS dstL dstR work) (L.choose h) (roundTime L h)
    ?start ?round ?done ?bound (hT := by first
                                         |
                                           ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                 List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, roundTime]);
                                             (first
                                               | omega
                                               | ((ring_nf); (omega))))
                                         | omega
                                         |
                                           (simp [roundTime] <;>
                                               first
                                               | omega
                                               | ((ring_nf); (omega))))) ?after
  case start =>
    refine ⟨0,0,0,0,μ₁,?_,hlefts,?_,?_⟩
    · simp [update_frame_setLocal]
      change frame [(L : ℤ),h,srcS,dstL,dstR,work,L.choose h,
        subsetMask (Finset.univ : Finset (Fin L)),0,0] =
        frame ([(L : ℤ),h,srcS,dstL,dstR,work,L.choose h,
          subsetMask (Finset.univ : Finset (Fin L)),0,0] ++ [0,0,0,0])
      exact (frame_append_zeros _ 4).symm
    · intro i hi; omega
    · intro i hi
      exact hkeepLayer i ⟨by omega,Or.inl hi⟩
  case round =>
    rintro j _ hj _ ⟨a,b,nr,r,μ',rfl,hlefts,hout,hkeep⟩
    have hjD : j*(L-h).choose h+(L-h).choose h ≤ L.choose h*(L-h).choose h := by
      have hm := Nat.mul_le_mul_right ((L-h).choose h) (show j+1 ≤ L.choose h by omega)
      nlinarith
    have hleftCard := leftAt_card hj
    have hcomp : (Finset.univ \ leftAt L h j).card = L-h := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin,hleftCard]
    have hread : μ' (srcS+j) = (subsetMask (leftAt L h j) : ℤ) := by
      have hget := hlefts j (by simpa only [List.length_map,enumerateLayer_length] using hj)
      simpa only [List.getElem_map,leftAt_mask hj] using hget
    have hlword := hmask (leftAt L h j)
    have hcword := hmask (Finset.univ \ leftAt L h j)
    have hdiff := MaskDifference.subsetMask_sdiff_int Finset.univ (leftAt L h j) (Finset.subset_univ _)
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
      (refine Light.Ends.setToThen (subsetMask (leftAt L h j) : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hread,
                  roundTime]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hread, roundTime] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hread, roundTime] <;>
                omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine
          Light.Ends.setToThen (subsetMask (Finset.univ \ leftAt L h j) : ℕ) ?_ ?_
            ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hdiff,
                  roundTime]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hdiff, roundTime] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hdiff, roundTime] <;>
                omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    have hq := LightQueryEnumeration.meets (P := program) (pMain := 0) (pWeights := 1)
      (pPowers := 2) (pErase := 3) (pEnum := 4) (d := d+1) (μ := μ')
      (dst := dstR+j*(L-h).choose h) (work := work) (t := h)
      rfl rfl rfl rfl rfl (Finset.univ \ leftAt L h j) hw (by omega) hword
      (by rw [hcomp]; omega) (by rw [hcomp]; omega) (by omega)
    rw [hcomp] at hq
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
        | refine Light.Ends.callToThen (hq _ (by omega)) ?_ ?_ ?_ ?_
        | refine Light.Ends.callToThen hq ?_ ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  roundTime]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [roundTime] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 => omega);
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, roundTime] <;> omega)));
      (on_goal -1 =>
          ((rintro count ν ⟨hcount, hnewR, hweights, hkeepQuery⟩);
            (try with_unfolding_none refine Light.Ends.skip ?_)))
    have ha := LightReportingAffine.meets (P := program) (p := 6) (d := d+1)
      (μ := ν) (src := dstR+j*(L-h).choose h) (dst := dstL+j*(L-h).choose h)
      (n := (L-h).choose h) (b := (subsetMask (leftAt L h j) : ℤ)) (c := 0)
      rfl hw (by omega) (by omega) (Or.inr (by omega))
      (by intro i hi; simp only [zero_mul,abs_zero]; omega)
      (by intro i hi; simpa only [zero_mul,add_zero,Int.abs_natCast] using hlword)
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
        | refine Light.Ends.callToThen (ha _ (by omega)) ?_ ?_ ?_ ?_
        | refine Light.Ends.callToThen ha ?_ ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hcount,
                  roundTime]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hcount, roundTime] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 => omega);
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hcount, roundTime] <;>
                omega)));
      (on_goal -1 =>
          ((rintro affineRet ξ ⟨hnewL, hkeepAffine⟩);
            (try with_unfolding_none refine Light.Ends.skip ?_)))
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen ((j + 1) * (L - h).choose h : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hcount,
                  Nat.add_mul, roundTime]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hcount, Nat.add_mul, roundTime] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hcount, Nat.add_mul,
                  roundTime] <;>
                omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    refine ⟨by simp,(subsetMask (leftAt L h j) : ℤ),
      (subsetMask (Finset.univ \ leftAt L h j) : ℤ),count,affineRet,ξ,?_,?_,?_,?_⟩
    · simp [update_frame_setLocal]
    · intro i hi
      rw [hkeepAffine (srcS+i) (Or.inl (by simp only [List.length_map,enumerateLayer_length] at hi; omega)),
        hkeepQuery (srcS+i) ⟨by simp only [List.length_map,enumerateLayer_length] at hi; omega,
          Or.inl (by simp only [List.length_map,enumerateLayer_length] at hi; omega)⟩]
      exact hlefts i hi
    · intro i hi l hl
      by_cases he : i = j
      · subst i
        constructor
        · simpa only [zero_mul,add_zero,Nat.add_assoc] using hnewL l hl
        · rw [hkeepAffine _ (Or.inr (by omega))]
          have hlen : l < (rights (leftAt L h j) h).length := by rw [rights_length _ hleftCard]; exact hl
          have hr := hnewR l (by simpa only [List.length_map,rights] using hlen)
          simpa only [List.getElem_map,Nat.add_assoc,rights,rightAt_eq_get hj hl] using hr
      · have hij : i < j := by omega
        have hm := Nat.mul_le_mul_right ((L-h).choose h) (show i+1 ≤ j by omega)
        obtain ⟨hprevL,hprevR⟩ := hout i hij l hl
        constructor
        · rw [hkeepAffine _ (Or.inl (by nlinarith)),hkeepQuery _ ⟨by nlinarith,Or.inl (by nlinarith)⟩]
          exact hprevL
        · rw [hkeepAffine _ (Or.inr (by omega)),hkeepQuery _ ⟨by nlinarith,Or.inl (by nlinarith)⟩]
          exact hprevR
    · intro i hi
      exact (hkeepAffine i (Or.inl (by omega))).trans
        ((hkeepQuery i ⟨by omega,Or.inl (by omega)⟩).trans (hkeep i hi))
  case done =>
    intro σ _ hσ
    exact hσ
  case bound =>
    rintro j _ hj _ ⟨a,b,nr,r,μ',rfl,_,_,_⟩
    (((try have := Light.Std.space_le (by assumption)));
      ((try have := Light.Std.const_le (by assumption)));
      (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))
  case after =>
    rintro _ ⟨a,b,nr,r,μ',rfl,hlefts,hout,hkeep⟩
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (L.choose h * (L - h).choose h : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  roundTime]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [roundTime] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, roundTime] <;> omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    refine ⟨?_,hlefts,hout,hkeep⟩
    simp only [LayerCounts.vertex_degree_identity]
    rfl













end ThreeSum.LightReportingPairRows

end


theorem solution : ∀ {lim : Light.Limits} {μ : Nat → Int} {L h srcS dstL dstR work d : Nat},
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    @LE.le.{0} Nat instLENat
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)
        L →
      @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcS (L.choose h))
          dstL →
        @LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dstL
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (L.choose h)
                ((@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) L h).choose h)))
            dstR →
          @LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dstR
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (L.choose h)
                  ((@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) L h).choose h)))
              work →
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                lim.space →
              @LE.le.{0} Int Int.instLEInt
                  (@Nat.cast.{0} Int instNatCastInt
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) L
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  lim.word →
                @LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d L)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    lim.depth →
                  Light.Meets lim ThreeSum.LightReportingPairRows.program
                    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) d
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt h)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcS)
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dstL)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dstR)
                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work) (@List.nil.{0} Int)))))))
                    μ (ThreeSum.LightReportingPairRows.time L h) fun (r : Int) (μ' : Nat → Int) =>
                    And
                      (@Eq.{1} Int r
                        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                          (@Nat.cast.{0} Int instNatCastInt
                            (L.choose
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)))
                          (@Nat.cast.{0} Int instNatCastInt
                            ((@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h).choose
                              h))))
                      (And (Light.SegN μ' srcS (ThreeSum.SubsetAddress.enumerateLayer L h))
                        (And
                          (∀ (i : Nat),
                            @LT.lt.{0} Nat instLTNat i (L.choose h) →
                              ∀ (j : Nat),
                                @LT.lt.{0} Nat instLTNat j
                                    ((@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) L h).choose h) →
                                  And
                                    (@Eq.{1} Int
                                      (μ'
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dstL
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i
                                              ((@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) L
                                                    h).choose
                                                h)))
                                          j))
                                      (@Nat.cast.{0} Int instNatCastInt
                                        (@ThreeSum.SubsetAddress.subsetMask L
                                          (ThreeSum.ReportingHostPairEnumeration.leftAt L h i))))
                                    (@Eq.{1} Int
                                      (μ'
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dstR
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i
                                              ((@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) L
                                                    h).choose
                                                h)))
                                          j))
                                      (@Nat.cast.{0} Int instNatCastInt
                                        (@ThreeSum.SubsetAddress.subsetMask L
                                          (ThreeSum.ReportingHostPairEnumeration.rightAt L h i j)))))
                          (Light.Kept μ μ' srcS))) := by
  exact @ThreeSum.LightReportingPairRows.program_meets_sourceProof

#print axioms solution
