-- Prove2me | solution 1 for ThreeSum.LightReportingPrefixArrays.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:32:39.033489+00:00
-- url     : https://prove2.me/submissions/5729eae0-c83d-4d2d-ae1a-71b1faa4acb7

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
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
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
import Mathlib.Data.List.TakeDrop
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
import Theorems.Thm_Light_powTable_ends
import Theorems.Thm_Light_seg_append
import Theorems.Thm_ThreeSum_LightRadixKeys_meets
import Theorems.Thm_ThreeSum_LightReportingPairRows_program_meets
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_leftAt_card
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_lefts_length
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_pairs_length
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_rights_length


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace Light.PowTable
end Light.PowTable
namespace ThreeSum.LayerCounts
end ThreeSum.LayerCounts
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.ReportingHostPairEnumeration
end ThreeSum.ReportingHostPairEnumeration
namespace ThreeSum.ReportingHostPairSegments
end ThreeSum.ReportingHostPairSegments
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

/-- A procedure of a program is a procedure, with the same number, of the program with more
procedures appended. -/
theorem getElem?_append_of_eq_some {P : Program} {p : ℕ} {body : Stmt} (h : P[p]? = some body)
    (R : Program) : (P ++ R)[p]? = some body := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h














/-- A run stays a run when procedures are appended to the program. -/
theorem Exec.append {s : Stmt} {σ σ' : State} {c : ℕ} (h : Exec lim P d s σ σ' c) (R : Program) :
    Exec lim (P ++ R) d s σ σ' c := by
  induction h with
  | skip => exact .skip
  | set h => exact .set h
  | store h₁ h₂ h₃ => exact .store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact .iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact .iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact .whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact .whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact .call h₁ (getElem?_append_of_eq_some h₂ R) h₃ ih

/-! ## The rules -/






/-- More time and a weaker conclusion. -/
theorem Ends.mono {s σ T T' Q Q'} (h : Ends lim P d s σ T Q) (hT : T ≤ T')
    (hQ : ∀ σ', Q σ' → Q' σ') : Ends lim P d s σ T' Q' := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he, hc.trans hT, hQ _ hq⟩

/-- What is proved about a program holds for the program with more procedures appended. -/
theorem Ends.append {s σ T Q} (h : Ends lim P d s σ T Q) (R : Program) :
    Ends lim (P ++ R) d s σ T Q := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he.append R, hc, hq⟩

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

/-- More time and a weaker conclusion. -/
theorem Meets.mono (h : Meets lim P p d vals μ T R) (hT : T ≤ T') (hR : ∀ r μ', R r μ' → R' r μ') :
    Meets lim P p d vals μ T' R' := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, hp, he.mono hT fun _ => hR _ _⟩











/-- A specification holds for the program with more procedures appended. -/
theorem Meets.append (h : Meets lim P p d vals μ T R) (P' : Program) :
    Meets lim (P ++ P') p d vals μ T R := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, getElem?_append_of_eq_some hp P', he.append P'⟩

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
# Tables of powers

powTable(dst, L, b) writes 1, b, b², …, b^(L-1) into the L cells from dst and changes nothing else,
within `powTableTime L` steps (`powTable_meets`).  The list of these powers is `powList b L`.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}




@[simp] theorem length_powList (b L : ℕ) : (powList b L).length = L := by simp [powList]

@[simp] theorem getElem_powList {b L j : ℕ} (h : j < (powList b L).length) :
    (powList b L)[j] = ((b ^ j : ℕ) : ℤ) := by
  simp [powList]

namespace PowTable









end PowTable

open PowTable


























































/-- **powTable(dst, L, b)** writes the powers 1, b, …, b^(L-1) into the L cells from dst and changes
nothing else. -/
theorem powTable_meets {p : ℕ} (hp : P[p]? = some powTableBody) {μ : ℕ → ℤ} {dst L b : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + L ≤ lim.space)
    (hpow : ∀ j ≤ L, ((b ^ j : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [(dst : ℤ), L, b] μ (powTableTime L) fun _ μ' =>
      Seg μ' dst (powList b L) ∧ SameOutside μ μ' dst L :=
  -- the local variables that are no arguments hold 0
  .of_body hp (frame_append_zeros [(dst : ℤ), L, b] 2 ▸ powTable_ends 0 0 [] hw hdst hpow)

end Light

end
end

section


/-!
# Machine evaluation of compact subset addresses

The current width decreases by one in each recursive call. Its highest
power of two is read from a table, so neither division nor a loop proportional
to the numeric bit-mask value occurs. Pascal coefficients are single reads
from the constructed rectangular table.
-/

namespace ThreeSum.LightSubsetAddress

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal

variable {lim : Limits} {P : Program}




theorem powers_of_segment {μ : ℕ → ℤ} {base W : ℕ}
    (h : Seg μ base (powList 2 (W+1))) : Powers μ base W := by
  intro i hi
  have hs := h i (by simp; omega)
  simpa only [getElem_powList] using hs

























































































































end ThreeSum.LightSubsetAddress

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
































































































theorem leftAt_eq_get {L h i : ℕ} (hi : i < L.choose h) :
    leftAt L h i = (lefts L h)[i]'(by simpa using hi) := by
  simp [leftAt,List.getElem?_eq_getElem,hi]





theorem rightAt_eq_get {L h i j : ℕ} (hi : i < L.choose h) (hj : j < (L-h).choose h) :
    rightAt L h i j = (rights (leftAt L h i) h)[j]'(by rw [rights_length _ (leftAt_card hi)]; exact hj) := by
  have hlen : j < (rights (leftAt L h i) h).length := by rw [rights_length _ (leftAt_card hi)]; exact hj
  simp [rightAt,List.getElem?_eq_getElem hlen]

























end ThreeSum.ReportingHostPairEnumeration

end

section


/-! # The constructed local pair arrays are aligned segments in one exact record order -/

namespace ThreeSum.ReportingHostPairSegments

open Light ThreeSum.SubsetAddress ReportingHostPairEnumeration

set_option linter.unusedSimpArgs false

variable {α β : Type*}

theorem seg_flatMap_uniform {μ : ℕ → ℤ} {dst n : ℕ} (xs : List α) (f : α → List ℤ)
    (hlen : ∀ x ∈ xs, (f x).length = n)
    (hout : ∀ i (hi : i < xs.length), ∀ j (hj : j < n),
      μ (dst+i*n+j) = (f xs[i])[j]'(by rw [hlen _ (List.getElem_mem hi)]; exact hj)) :
    Seg μ dst (xs.flatMap f) := by
  induction xs generalizing dst with
  | nil => simp [Seg,SegN]
  | cons x xs ih =>
    rw [List.flatMap_cons]
    apply seg_append.mpr
    constructor
    · intro j hj
      have hn : j < n := by rw [← hlen x (by simp)]; exact hj
      have hh := hout 0 (by simp) j hn
      simp only [Nat.zero_mul,Nat.add_zero] at hh
      change μ (dst+j) = (f x)[j] at hh
      exact hh
    · rw [hlen x (by simp)]
      apply ih (by intro a ha; exact hlen a (by simp [ha]))
      intro i hi j hj
      have hh := hout (i+1) (by simpa using hi) j hj
      simpa only [List.getElem_cons_succ,Nat.add_mul,Nat.one_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
        using hh




@[simp] theorem leftMasks_length (L h : ℕ) : (leftMasks L h).length = L.choose (2*h)*(2*h).choose h := by
  simp [leftMasks,pairs_length]

@[simp] theorem rightMasks_length (L h : ℕ) : (rightMasks L h).length = L.choose (2*h)*(2*h).choose h := by
  simp [rightMasks,pairs_length]

theorem leftMasks_bounded (L h : ℕ) : ∀ x ∈ leftMasks L h, |x| ≤ ((2^L : ℕ) : ℤ) := by
  intro x hx
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx
  rw [Int.abs_natCast]
  exact Int.ofNat_le.mpr (Nat.le_of_lt (subsetMask_isMask p.1).1)

theorem rightMasks_bounded (L h : ℕ) : ∀ x ∈ rightMasks L h, |x| ≤ ((2^L : ℕ) : ℤ) := by
  intro x hx
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx
  rw [Int.abs_natCast]
  exact Int.ofNat_le.mpr (Nat.le_of_lt (subsetMask_isMask p.2).1)

theorem leftMasks_of_rows {μ : ℕ → ℤ} {L h dst : ℕ}
    (hout : ∀ i < L.choose h, ∀ j < (L-h).choose h,
      μ (dst+i*(L-h).choose h+j) = (subsetMask (leftAt L h i) : ℤ)) :
    Seg μ dst (leftMasks L h) := by
  unfold leftMasks pairs
  rw [List.map_flatMap]
  simp only [List.map_map,Function.comp_def]
  apply seg_flatMap_uniform (n := (L-h).choose h) (lefts L h)
    (fun S => (rights S h).map (fun _ => (subsetMask S : ℤ)))
    (by intro S hS; simpa using rights_length S ((lefts_mem S).mp hS))
  intro i hi j hj
  have hin : i < L.choose h := by simpa using hi
  have hh := hout i hin j hj
  simpa only [List.getElem_map,leftAt_eq_get hin] using hh

theorem rightMasks_of_rows {μ : ℕ → ℤ} {L h dst : ℕ}
    (hout : ∀ i < L.choose h, ∀ j < (L-h).choose h,
      μ (dst+i*(L-h).choose h+j) = (subsetMask (rightAt L h i j) : ℤ)) :
    Seg μ dst (rightMasks L h) := by
  unfold rightMasks pairs
  rw [List.map_flatMap]
  simp only [List.map_map,Function.comp_def]
  apply seg_flatMap_uniform (n := (L-h).choose h) (lefts L h)
    (fun S => (rights S h).map (fun R => (subsetMask R : ℤ)))
    (by intro S hS; simpa using rights_length S ((lefts_mem S).mp hS))
  intro i hi j hj
  have hin : i < L.choose h := by simpa using hi
  have hh := hout i hin j hj
  simpa only [List.getElem_map,rightAt_eq_get hin hj,leftAt_eq_get hin] using hh

theorem program_meets {lim : Limits} {μ : ℕ → ℤ} {L h srcS dstL dstR work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hh : 2*h ≤ L)
    (hS : srcS+L.choose h ≤ dstL)
    (hL : dstL+L.choose h*(L-h).choose h ≤ dstR)
    (hR : dstR+L.choose h*(L-h).choose h ≤ work)
    (hspace : work+2*L+2 ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+L+3 ≤ lim.depth) :
    Meets lim LightReportingPairRows.program 7 d [L,h,srcS,dstL,dstR,work]
      μ (LightReportingPairRows.time L h)
      (fun r μ' => r = (L.choose (2*h)*(2*h).choose h : ℤ) ∧
        Seg μ' dstL (leftMasks L h) ∧ Seg μ' dstR (rightMasks L h) ∧ Kept μ μ' srcS) := by
  apply (LightReportingPairRows.program_meets hw hh hS hL hR hspace hword hd).mono le_rfl
  rintro r μ' ⟨hr,_,hout,hkeep⟩
  exact ⟨hr,leftMasks_of_rows (by intro i hi j hj; exact (hout i hi j hj).1),
    rightMasks_of_rows (by intro i hi j hj; exact (hout i hi j hj).2),hkeep⟩

end ThreeSum.ReportingHostPairSegments

end

section


/-!
# Exact product-list semantics for global radix-key construction

The key list retains every local occurrence, even when several records have
the same integer key. Each stage prepends one local record and computes its
positional hash. This is the order used by the concrete row constructor.
-/

namespace ThreeSum.RadixKeyLists

variable {α β : Type*}













theorem step_length (p : ℤ) (base prev : List ℤ) :
    (step p base prev).length=base.length*prev.length :=
  flatMap_length_uniform base _ prev.length (by simp)











theorem values_length (p : ℤ) (base : List ℤ) (j : ℕ) :
    (values p base j).length=base.length^j := by
  induction j with
  | zero => simp [values]
  | succ j ih => rw [values,step_length,ih,pow_succ']

















































































end ThreeSum.RadixKeyLists

end

section


/-!
# Constructing both complete prefix-mask product arrays in the same record order

The local pair arrays are built directly, then the verified positional-key
host is used twice with radix 2^L. Both results share the literal tuple order,
including separate entries for pairs with equal left or right projections.
-/

namespace ThreeSum.LightReportingPrefixArrays

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostPairEnumeration ReportingHostPairSegments

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000

variable {lim : Limits}

















theorem program_meets_sourceProof {μ : ℕ → ℤ} {L h k srcS pairL pairR stageL stageR work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hh : 2*h ≤ L)
    (hS : srcS+L.choose h ≤ pairL)
    (hL : pairL+localCount L h ≤ pairR) (hR : pairR+localCount L h ≤ stageL)
    (hstageL : LightRadixKeys.space stageL (localCount L h) k ≤ stageR)
    (hstageR : LightRadixKeys.space stageR (localCount L h) k ≤ work)
    (hspace : work+2*L+2 ≤ lim.space)
    (hpowWord : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hkeysWord : (LightRadixKeys.word (2^L) (2^L) k : ℤ) ≤ lim.word)
    (hd : d+L+k+4 ≤ lim.depth) :
    Meets lim program 10 d [L,h,k,srcS,pairL,pairR,stageL,stageR,work] μ (time L h k)
      (fun r μ' =>
        r = (stageL+LightRadixKeys.offset (localCount L h) k : ℕ) ∧
        μ' (stageL+LightRadixKeys.offset (localCount L h) k) = ((localCount L h)^k : ℕ) ∧
        μ' (stageR+LightRadixKeys.offset (localCount L h) k) = ((localCount L h)^k : ℕ) ∧
        Seg μ' (stageL+LightRadixKeys.offset (localCount L h) k+1)
          (RadixKeyLists.values ((2^L : ℕ) : ℤ) (leftMasks L h) k) ∧
        Seg μ' (stageR+LightRadixKeys.offset (localCount L h) k+1)
          (RadixKeyLists.values ((2^L : ℕ) : ℤ) (rightMasks L h) k) ∧
        Kept μ μ' srcS) := by
  have hpos : 0 < localCount L h := Nat.mul_pos (Nat.choose_pos hh) (Nat.choose_pos (by omega))
  have hleftLen : (leftMasks L h).length = localCount L h := leftMasks_length L h
  have hrightLen : (rightMasks L h).length = localCount L h := rightMasks_length L h
  have hstageOrder : stageL ≤ stageR := by unfold LightRadixKeys.space at hstageL; omega
  have hworkOrder : stageR ≤ work := by unfold LightRadixKeys.space at hstageR; omega
  have hpowBound : ∀ j ≤ L+1, ((2^j : ℕ) : ℤ) ≤ lim.word := by
    intro j hj
    exact (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) hj)).trans hpowWord
  have hpairProd : L.choose h*(L-h).choose h = localCount L h := LayerCounts.vertex_degree_identity L h
  apply Meets.of_body (p := 10) (by rfl : program[10]? = some (body 7 2 8))
  unfold body time
  have hp := (ReportingHostPairSegments.program_meets (d := d+1) (μ := μ)
    (L := L) (h := h) (srcS := srcS) (dstL := pairL) (dstR := pairR) (work := work)
    hw hh hS (by simpa only [hpairProd] using hL) (by rw [hpairProd]; omega) hspace hpowWord (by omega)).append
      [LightRadixKeys.body 8 9,LightRadixRows.body 6,body 7 2 8]
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
      | refine Light.Ends.callToThen (hp _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hp ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightReportingPairRows.time, LightRadixKeys.time, powTableTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightReportingPairRows.time, LightRadixKeys.time,
                powTableTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, LightReportingPairRows.time,
                LightRadixKeys.time, powTableTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro count μ₁ ⟨hcount, hleft, hright, hkeepPair⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hcount' : count = (localCount L h : ℤ) := hcount
  have hpow := powTable_meets (P := program) (p := 2) (d := d+1) (μ := μ₁)
    (dst := work) (L := L+1) (b := 2) rfl hw (by omega) hpowBound
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
      | refine Light.Ends.callToThen (hpow _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hpow ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightReportingPairRows.time, LightRadixKeys.time, powTableTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightReportingPairRows.time, LightRadixKeys.time,
                powTableTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, LightReportingPairRows.time,
                LightRadixKeys.time, powTableTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro powRet μ₂ ⟨hpowers, hkeepPowers⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hreadPow := powers_of_segment hpowers L le_rfl
  have hreadPowNat : μ₂ (work+L) = ((2^L : ℕ) : ℤ) := by simpa using hreadPow
  have hradix := hpowBound L (by omega)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (2 ^ L : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hreadPow, hreadPowNat, LightReportingPairRows.time,
                LightRadixKeys.time, powTableTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hreadPow, hreadPowNat, LightReportingPairRows.time,
                LightRadixKeys.time, powTableTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hreadPow, hreadPowNat,
                LightReportingPairRows.time, LightRadixKeys.time,
                powTableTime] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  have hleft₂ : Seg μ₂ pairL (leftMasks L h) := by
    intro i hi
    rw [hkeepPowers _ (Or.inl (by rw [hleftLen] at hi; omega))]
    exact hleft i hi
  have hright₂ : Seg μ₂ pairR (rightMasks L h) := by
    intro i hi
    rw [hkeepPowers _ (Or.inl (by rw [hrightLen] at hi; omega))]
    exact hright i hi
  have hl := LightRadixKeys.meets (P := program) (pMain := 8) (pRows := 9) (pAffine := 6)
    (src := pairL) (dst := stageL) (p := 2^L) (U := 2^L) rfl rfl rfl
    (leftMasks L h) hw (by rw [hleftLen]; omega) (by rw [hleftLen]; exact hpos)
    (leftMasks_bounded L h) k (d+1) μ₂
    (by rw [hleftLen]; exact hstageL.trans (by omega)) hkeysWord (by omega) hleft₂
  simp only [hleftLen] at hl
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
      | refine Light.Ends.callToThen (hl _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hl ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hcount',
                LightReportingPairRows.time, LightRadixKeys.time, powTableTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hcount', LightReportingPairRows.time, LightRadixKeys.time,
                powTableTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hcount',
                LightReportingPairRows.time, LightRadixKeys.time,
                powTableTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro leftHead μ₃ ⟨hleftHead, hleftHeader, hleftArray, hkeepLeft⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hright₃ : Seg μ₃ pairR (rightMasks L h) := by
    intro i hi
    rw [hkeepLeft _ (by rw [hrightLen] at hi; omega)]
    exact hright₂ i hi
  have hr := LightRadixKeys.meets (P := program) (pMain := 8) (pRows := 9) (pAffine := 6)
    (src := pairR) (dst := stageR) (p := 2^L) (U := 2^L) rfl rfl rfl
    (rightMasks L h) hw (by rw [hrightLen]; omega) (by rw [hrightLen]; exact hpos)
    (rightMasks_bounded L h) k (d+1) μ₃
    (by rw [hrightLen]; exact hstageR.trans (by omega)) hkeysWord (by omega) hright₃
  simp only [hrightLen] at hr
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
      | refine Light.Ends.callToThen (hr _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hr ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hcount',
                LightReportingPairRows.time, LightRadixKeys.time, powTableTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hcount', LightReportingPairRows.time, LightRadixKeys.time,
                powTableTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hcount',
                LightReportingPairRows.time, LightRadixKeys.time,
                powTableTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro rightHead μ₄
              ⟨hrightHead, hrightHeader, hrightArray, hkeepRight⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hleftBound : stageL+LightRadixKeys.offset (localCount L h) k+1+(localCount L h)^k ≤ stageR := hstageL
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
        Light.Ends.setToThen
          (stageL + LightRadixKeys.offset (localCount L h) k : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hleftHead, LightReportingPairRows.time, LightRadixKeys.time,
                powTableTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hleftHead, LightReportingPairRows.time, LightRadixKeys.time,
                powTableTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hleftHead,
                LightReportingPairRows.time, LightRadixKeys.time,
                powTableTime] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  refine ⟨by simp,?_,hrightHeader,?_,hrightArray,?_⟩
  · change μ₄ (stageL+LightRadixKeys.offset (localCount L h) k) = _
    rw [hkeepRight _ (by omega)]
    exact hleftHeader
  · intro i hi
    change μ₄ (stageL+LightRadixKeys.offset (localCount L h) k+1+i) = _
    rw [hkeepRight _ (by simp only [RadixKeyLists.values_length,hleftLen] at hi; omega)]
    exact hleftArray i hi
  · intro i hi
    exact (hkeepRight i (by omega)).trans ((hkeepLeft i (by omega)).trans
      ((hkeepPowers i (Or.inl (by omega))).trans (hkeepPair i hi)))











end ThreeSum.LightReportingPrefixArrays

end


theorem solution : ∀ {lim : Light.Limits} {μ : Nat → Int} {L h k srcS pairL pairR stageL stageR work d : Nat},
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    @LE.le.{0} Nat instLENat
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)
        L →
      @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcS (L.choose h))
          pairL →
        @LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pairL
              (ThreeSum.LightReportingPrefixArrays.localCount L h))
            pairR →
          @LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pairR
                (ThreeSum.LightReportingPrefixArrays.localCount L h))
              stageL →
            @LE.le.{0} Nat instLENat
                (ThreeSum.LightRadixKeys.space stageL (ThreeSum.LightReportingPrefixArrays.localCount L h) k) stageR →
              @LE.le.{0} Nat instLENat
                  (ThreeSum.LightRadixKeys.space stageR (ThreeSum.LightReportingPrefixArrays.localCount L h) k) work →
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
                    @LE.le.{0} Int Int.instLEInt
                        (@Nat.cast.{0} Int instNatCastInt
                          (ThreeSum.LightRadixKeys.word
                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)
                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)
                            k))
                        lim.word →
                      @LE.le.{0} Nat instLENat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d L) k)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                          lim.depth →
                        Light.Meets lim ThreeSum.LightReportingPrefixArrays.program
                          (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) d
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt h)
                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt k)
                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcS)
                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt pairL)
                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt pairR)
                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt stageL)
                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt stageR)
                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                            (@List.nil.{0} Int))))))))))
                          μ (ThreeSum.LightReportingPrefixArrays.time L h k) fun (r : Int) (μ' : Nat → Int) =>
                          And
                            (@Eq.{1} Int r
                              (@Nat.cast.{0} Int instNatCastInt
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) stageL
                                  (ThreeSum.LightRadixKeys.offset (ThreeSum.LightReportingPrefixArrays.localCount L h)
                                    k))))
                            (And
                              (@Eq.{1} Int
                                (μ'
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) stageL
                                    (ThreeSum.LightRadixKeys.offset (ThreeSum.LightReportingPrefixArrays.localCount L h)
                                      k)))
                                (@Nat.cast.{0} Int instNatCastInt
                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                    (@instHPow.{0, 0} Nat Nat
                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                    (ThreeSum.LightReportingPrefixArrays.localCount L h) k)))
                              (And
                                (@Eq.{1} Int
                                  (μ'
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) stageR
                                      (ThreeSum.LightRadixKeys.offset
                                        (ThreeSum.LightReportingPrefixArrays.localCount L h) k)))
                                  (@Nat.cast.{0} Int instNatCastInt
                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                      (@instHPow.{0, 0} Nat Nat
                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                      (ThreeSum.LightReportingPrefixArrays.localCount L h) k)))
                                (And
                                  (Light.Seg μ'
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) stageL
                                        (ThreeSum.LightRadixKeys.offset
                                          (ThreeSum.LightReportingPrefixArrays.localCount L h) k))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    (ThreeSum.RadixKeyLists.values
                                      (@Nat.cast.{0} Int instNatCastInt
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L))
                                      (ThreeSum.ReportingHostPairSegments.leftMasks L h) k))
                                  (And
                                    (Light.Seg μ'
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) stageR
                                          (ThreeSum.LightRadixKeys.offset
                                            (ThreeSum.LightReportingPrefixArrays.localCount L h) k))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                      (ThreeSum.RadixKeyLists.values
                                        (@Nat.cast.{0} Int instNatCastInt
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L))
                                        (ThreeSum.ReportingHostPairSegments.rightMasks L h) k))
                                    (Light.Kept μ μ' srcS))))) := by
  exact @ThreeSum.LightReportingPrefixArrays.program_meets_sourceProof

#print axioms solution
