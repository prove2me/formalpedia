-- Prove2me | solution 1 for ThreeSum.LightReportingCatalogLookup.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:02:16.303965+00:00
-- url     : https://prove2.me/submissions/25541854-48fb-4415-bf36-1c6119a70ee0

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
import Definitions.Def_ThreeSum1962Source_Bundle13
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
import Mathlib.Data.Finset.Basic
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
import Theorems.Thm_Light_emod_meets
import Theorems.Thm_Light_powTable_ends
import Theorems.Thm_ThreeSum_BinarySearch_upperSearch_correct
import Theorems.Thm_ThreeSum_LightBandLookup_search_meets
import Theorems.Thm_ThreeSum_ReportingHostPackedCatalog_upperBound_hit


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace Light.PowTable
end Light.PowTable
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.ReportingHostPackedCatalog
end ThreeSum.ReportingHostPackedCatalog
namespace ThreeSum.ReportingHostPrefixCatalog
end ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum.ReportingHostPrefixOrder
end ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# Executable binary search with a comparison budget

`upperSearch` finds the first array entry strictly above a query.  Its fuel is
logarithmic, and the proof accounts for the actual branches taken.  Array
accesses here are explicit function calls; a machine realization must still
implement those calls by bounded-address loads.
-/

namespace ThreeSum.BinarySearch













































































theorem upperBound_correct (f : ℕ → ℤ) (n : ℕ) (x : ℤ)
    (hsorted : ∀ i j, i ≤ j → j < n → f i ≤ f j) :
    Partition f x n (upperBound f n x) := by
  apply upperSearch_correct f x n (Nat.log 2 n + 1) 0 n hsorted (by omega) (by omega)
  · simpa only [Nat.sub_zero] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  · intro i hi; omega
  · intro i hi hin; omega

















































end ThreeSum.BinarySearch

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
# Exact sorted lookup of a prefix catalog record

Each original catalog position is retained as the low digit of a packed
integer. A sorted search uses the upper end of the requested key's interval;
the unique prefix-key proof forces that hit to be the original record, and
remainder recovers its unchanged catalog index.
-/

namespace ThreeSum.ReportingHostPackedCatalog

open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPrefixOrder

set_option maxHeartbeats 600000







theorem codes_length (key : ℕ → ℕ) (n : ℕ) : (codes key n).length=n := by simp [codes]

theorem pairKey_lt {radix left right : ℕ} (hl : left < radix) (hr : right < radix) :
    pairKey radix left right < radix^2 := by unfold pairKey; nlinarith










theorem packed_lt {key : ℕ → ℕ} {n i U : ℕ} (hi : i < n) (hk : key i < U) :
    packed key n i < U*(n+1) := by unfold packed; nlinarith

theorem packed_mod {key : ℕ → ℕ} {n i : ℕ} (hi : i < n) : packed key n i%(n+1)=i := by
  simp [packed,Nat.add_mod,Nat.mod_eq_of_lt (show i < n+1 by omega)]

theorem packed_emod {key : ℕ → ℕ} {n i : ℕ} (hi : i < n) :
    ((packed key n i : ℕ) : ℤ)%((n+1 : ℕ) : ℤ) = (i : ℤ) := by
  exact_mod_cast packed_mod (key := key) hi


















theorem sorted_getD_le {S : List ℤ} (hs : S.Pairwise (· ≤ ·)) :
    ∀ i j, i ≤ j → j < S.length → S.getD i 0 ≤ S.getD j 0 := by
  intro i j hij hj
  by_cases he : i=j
  · subst j; exact le_rfl
  · rw [List.getD_eq_getElem _ _ (by omega),List.getD_eq_getElem _ _ hj]
    exact List.pairwise_iff_getElem.mp hs i j (by omega) hj (by omega)












































































end ThreeSum.ReportingHostPackedCatalog

end

section


/-!
# The remainder of a division

emod(x, M, fr) returns the remainder of the integer x modulo M ≥ 1, a number in 0, …, M - 1.  The
language has no division: the routine writes M, 2M, 4M, … into a table at the free pointer fr as
long as they are at most |x|, subtracts them from |x| from the largest down where possible, and
corrects the sign (`emod_meets`).  With k = `emodRounds |x| M` doublings it takes `emodTime |x| M`
steps, a constant times k + 1, and k cells.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}
namespace Emod










end Emod

















































/-- There are at most log₂ (V + 1) + 1 doublings for a number up to V. -/
theorem emodRounds_le {a M V : ℕ} (ha : a ≤ V) : emodRounds a M ≤ Nat.log 2 (V + 1) + 1 := by
  rw [emodRounds, Nat.size_le]
  calc a / M ≤ a := Nat.div_le_self _ _
    _ < V + 1 := by omega
    _ < 2 ^ (Nat.log 2 (V + 1) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _

















namespace Emod













variable {μ : ℕ → ℤ} {x : ℤ} {Mo V fr a : ℕ}










































































































































end Emod

end Light

end
end

section


/-!
# Actual logarithmic lookup of an original prefix-catalog index

The program constructs its own powers, forms the physical query pair key,
performs division-free binary search over the sorted packed records, and
uses the benchmark's binary remainder algorithm to recover the original
catalog position. No full-catalog scan or index oracle occurs.
-/

namespace ThreeSum.LightReportingCatalogLookup

open Light ThreeSum.LightPascal ThreeSum.LightSubsetAddress ReportingHostPackedCatalog

set_option maxHeartbeats 1500000
set_option maxRecDepth 8000

variable {lim : Limits}






theorem word_components (U n A B : ℕ) :
    U ≤ 4*U+4*(n+1)+n+A+B+16 ∧ A ≤ 4*U+4*(n+1)+n+A+B+16 ∧
    n+A+16 ≤ 4*U+4*(n+1)+n+A+B+16 ∧ 4*U+4*(n+1)+16 ≤ 4*U+4*(n+1)+n+A+B+16 := by omega

theorem word_value (W n : ℕ) : valueBound W n ≤ word W n := (word_components _ _ _ _).1
theorem word_power (W n : ℕ) : 2^(2*W+2) ≤ word W n := (word_components _ _ _ _).2.1
theorem word_search (W n : ℕ) : n+2^((2*W+1)+1)+16 ≤ word W n := (word_components _ _ _ _).2.2.1
theorem word_emod (W n : ℕ) : 4*valueBound W n+4*(n+1)+16 ≤ word W n := (word_components _ _ _ _).2.2.2














theorem program_meets_sourceProof {μ : ℕ → ℤ} {W n src work i d : ℕ} {S : List ℤ}
    (left right : ℕ → ℕ) (hi : i < n)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+n ≤ work) (hpowSpace : work+(2*W+2) ≤ lim.space)
    (hemodSpace : work+(Nat.log 2 (valueBound W n+1)+2) ≤ lim.space)
    (hword : (word W n : ℤ) ≤ lim.word)
    (hn : n ≤ 2^(2*W))
    (hboundL : ∀ j < n, left j < 2^W) (hboundR : ∀ j < n, right j < 2^W)
    (hunique : ∀ a < n, ∀ b < n,
      pairKey (2^W) (left a) (right a)=pairKey (2^W) (left b) (right b) → a=b)
    (hperm : S.Perm (codes (fun j => pairKey (2^W) (left j) (right j)) n))
    (hsorted : S.Pairwise (· ≤ ·)) (hseg : Seg μ src S)
    (hd : d+2*W+2 ≤ lim.depth) :
    Meets lim program 3 d [W,n,src,left i,right i,work] μ (time W n)
      (fun r μ' => r = (i : ℤ) ∧ Kept μ μ' work) := by
  let key : ℕ → ℕ := fun j => pairKey (2^W) (left j) (right j)
  let threshold : ℕ := key i*(n+1)+n
  let K := BinarySearch.upperBound (fun j => S.getD j 0) n (threshold : ℤ)
  have hlen : S.length=n := hperm.length_eq.trans (codes_length key n)
  have hkey : key i < 2^(2*W) := by
    simpa only [key,← pow_mul,Nat.mul_comm] using pairKey_lt (hboundL i hi) (hboundR i hi)
  have hthreshold : threshold < valueBound W n := by unfold threshold valueBound; nlinarith
  have hcode : packed key n i < valueBound W n := packed_lt hi hkey
  have hUword : (valueBound W n : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (word_value W n)).trans hword
  have hthWord : (threshold : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hthreshold.le).trans hUword
  have hcodeWord : (packed key n i : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hcode.le).trans hUword
  have hpowWord : ((2^(2*W+2) : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (word_power W n)).trans hword
  have hpowBound : ∀ j ≤ 2*W+2, ((2^j : ℕ) : ℤ) ≤ lim.word := by
    intro j hj
    exact (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) hj)).trans hpowWord
  have hsearchWord : ((n+2^((2*W+1)+1)+16 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (word_search W n)).trans hword
  have hEmod : Light.Emod.Pre lim (n+1) (valueBound W n) work :=
    ⟨by omega,hw,by
      have hh := (Int.ofNat_le.mpr (word_emod W n)).trans hword
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hh,hemodSpace⟩
  have hkeyN : key i ≤ valueBound W n := by unfold valueBound; nlinarith
  have hmulN : 2^W*right i ≤ valueBound W n := by unfold key pairKey at hkeyN; omega
  have hprodN : key i*(n+1) ≤ valueBound W n := by unfold threshold at hthreshold; omega
  have hmulZ : ((2^W : ℕ) : ℤ)*(right i : ℤ) ≤ lim.word :=
    (by exact_mod_cast hmulN : ((2^W : ℕ) : ℤ)*(right i : ℤ) ≤ (valueBound W n : ℤ)).trans hUword
  have hkeyZ : (left i : ℤ)+((2^W : ℕ) : ℤ)*(right i : ℤ) ≤ lim.word :=
    (by exact_mod_cast hkeyN : (left i : ℤ)+((2^W : ℕ) : ℤ)*(right i : ℤ) ≤ (valueBound W n : ℤ)).trans hUword
  have hprodZ : ((left i : ℤ)+((2^W : ℕ) : ℤ)*(right i : ℤ))*((n : ℤ)+1) ≤ lim.word :=
    (by exact_mod_cast hprodN :
      ((left i : ℤ)+((2^W : ℕ) : ℤ)*(right i : ℤ))*((n : ℤ)+1) ≤ (valueBound W n : ℤ)).trans hUword
  have hmul0 : 0 ≤ ((2^W : ℕ) : ℤ)*(right i : ℤ) := by positivity
  have hprod0 : 0 ≤ ((left i : ℤ)+((2^W : ℕ) : ℤ)*(right i : ℤ))*((n : ℤ)+1) := by positivity
  have hthZ : ((left i : ℤ)+((2^W : ℕ) : ℤ)*(right i : ℤ))*((n : ℤ)+1)+(n : ℤ) ≤ lim.word := by
    simpa only [threshold,key,pairKey,Nat.cast_add,Nat.cast_mul,Nat.cast_one] using hthWord
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hmulZ hkeyZ hprodZ hmul0 hprod0 hthZ
  have hhit := upperBound_hit hi hunique hperm hsorted
  change 0 < K ∧ K ≤ n ∧ S.getD (K-1) 0 = (packed key n i : ℤ) at hhit
  have hnWidth : n < 2^(2*W+1) := by
    have hp : 0 < 2^(2*W) := Nat.two_pow_pos _
    rw [pow_succ]
    omega
  apply Meets.of_body (p := 3) (by rfl : program[3]? = some (body 0 1 2))
  unfold body time
  have hp := powTable_meets (P := program) (p := 0) (d := d+1) (μ := μ)
    (dst := work) (L := 2*W+2) (b := 2) rfl hw hpowSpace hpowBound
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
                powTableTime, LightBandLookup.searchTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [powTableTime, LightBandLookup.searchTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, powTableTime,
                LightBandLookup.searchTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro powRet μ₁ ⟨hpowers, hkeepPowers⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hPowers : Powers μ₁ work (2*W+1) := powers_of_segment hpowers
  have hradius := hPowers W (by omega)
  have hradiusN : μ₁ (work+W) = ((2^W : ℕ) : ℤ) := by simpa using hradius
  have hradiusWord := hpowBound W (by omega)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (2 ^ W : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hradius,
                hradiusN, powTableTime, LightBandLookup.searchTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hradius, hradiusN, powTableTime, LightBandLookup.searchTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hradius, hradiusN,
                powTableTime, LightBandLookup.searchTime] <;>
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
    (refine Light.Ends.setToThen (threshold : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                threshold, key, pairKey, powTableTime,
                LightBandLookup.searchTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [threshold, key, pairKey, powTableTime,
                LightBandLookup.searchTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, threshold, key, pairKey,
                powTableTime, LightBandLookup.searchTime] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  have hread : ∀ j < n, μ₁ (src+j) = S.getD j 0 := by
    intro j hj
    exact (hkeepPowers _ (Or.inl (by omega))).trans (hseg.getD (by omega) 0)
  have hsort : ∀ a b, a ≤ b → b < n → S.getD a 0 ≤ S.getD b 0 := by
    simpa only [hlen] using sorted_getD_le hsorted
  have hsearch := LightBandLookup.search_meets (P := program) (pSearch := 1)
    (a := src) (n := n) (powers := work) (W := 2*W+1) (x := (threshold : ℤ)) rfl μ₁
    (fun j => S.getD j 0) K hw (hsrc.trans (by omega)) (by omega) hsearchWord hread hPowers
    (BinarySearch.upperBound_correct _ _ _ hsort) (2*W+1) 0 le_rfl (by omega)
    (by omega) (d+1) (by omega)
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
      | refine Light.Ends.callToThen (hsearch _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hsearch ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                threshold, powTableTime, LightBandLookup.searchTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [threshold, powTableTime, LightBandLookup.searchTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, threshold, powTableTime,
                LightBandLookup.searchTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro found μ₂ ⟨hfound, hmem⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  subst μ₂
  have hreadHit : μ₁ (src+(K-1)) = (packed key n i : ℤ) :=
    (hread _ (by omega)).trans hhit.2.2
  have hreadHitZ : μ₁ (((src : ℤ)+(K : ℤ)-1).toNat) = (packed key n i : ℤ) := by
    have ha : ((src : ℤ)+(K : ℤ)-1).toNat = src+(K-1) := by omega
    rw [ha]
    exact hreadHit
  have hreadHitSub : μ₁ (src+K-1) = (packed key n i : ℤ) := by
    have ha : src+K-1 = src+(K-1) := by omega
    rw [ha]
    exact hreadHit
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (packed key n i : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hfound,
                hreadHit, hreadHitZ, hreadHitSub, powTableTime,
                LightBandLookup.searchTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hfound, hreadHit, hreadHitZ, hreadHitSub, powTableTime,
                LightBandLookup.searchTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hfound, hreadHit, hreadHitZ,
                hreadHitSub, powTableTime, LightBandLookup.searchTime] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  have hem := emod_meets (P := program) (p := 2) (d := d+1) (μ := μ₁)
    (x := (packed key n i : ℤ)) rfl hEmod (by simpa only [Int.abs_natCast] using (Int.ofNat_le.mpr hcode.le))
  have hemTime : emodTime (packed key n i : ℤ).natAbs (n+1) ≤
      100*(Nat.log 2 (valueBound W n+1)+2) := by
    have hh := emodRounds_le (M := n+1) hcode.le
    simpa only [Int.natAbs_natCast,emodTime] using
      (show 43*emodRounds (packed key n i) (n+1)+34 ≤ 100*(Nat.log 2 (valueBound W n+1)+2) by omega)
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
          Light.Ends.callToThen ((hem.mono_time hemTime) _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen (hem.mono_time hemTime) ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                powTableTime, LightBandLookup.searchTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [powTableTime, LightBandLookup.searchTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, powTableTime,
                LightBandLookup.searchTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro index μ₃ ⟨hindex, hkeepEmod⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  refine ⟨hindex.trans (packed_emod hi),?_⟩
  intro j hj
  exact (hkeepEmod j hj).trans (hkeepPowers j (Or.inl hj))

end ThreeSum.LightReportingCatalogLookup

end


theorem solution : ∀ {lim : Light.Limits} {μ : Nat → Int} {W n src work i d : Nat} {S : List.{0} Int} (left right : Nat → Nat),
  @LT.lt.{0} Nat instLTNat i n →
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
      @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src n) work →
        @LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) W)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            lim.space →
          @LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (Nat.log (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (ThreeSum.LightReportingCatalogLookup.valueBound W n)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              lim.space →
            @LE.le.{0} Int Int.instLEInt
                (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightReportingCatalogLookup.word W n)) lim.word →
              @LE.le.{0} Nat instLENat n
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) W)) →
                (∀ (j : Nat),
                    @LT.lt.{0} Nat instLTNat j n →
                      @LT.lt.{0} Nat instLTNat (left j)
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) W)) →
                  (∀ (j : Nat),
                      @LT.lt.{0} Nat instLTNat j n →
                        @LT.lt.{0} Nat instLTNat (right j)
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) W)) →
                    (∀ (a : Nat),
                        @LT.lt.{0} Nat instLTNat a n →
                          ∀ (b : Nat),
                            @LT.lt.{0} Nat instLTNat b n →
                              @Eq.{1} Nat
                                  (ThreeSum.ReportingHostPackedCatalog.pairKey
                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                      (@instHPow.{0, 0} Nat Nat
                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) W)
                                    (left a) (right a))
                                  (ThreeSum.ReportingHostPackedCatalog.pairKey
                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                      (@instHPow.{0, 0} Nat Nat
                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) W)
                                    (left b) (right b)) →
                                @Eq.{1} Nat a b) →
                      @List.Perm.{0} Int S
                          (ThreeSum.ReportingHostPackedCatalog.codes
                            (fun (j : Nat) =>
                              ThreeSum.ReportingHostPackedCatalog.pairKey
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) W)
                                (left j) (right j))
                            n) →
                        @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LE.le.{0} Int Int.instLEInt x1 x2) S →
                          Light.Seg μ src S →
                            @LE.le.{0} Nat instLENat
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) W))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                lim.depth →
                              Light.Meets lim ThreeSum.LightReportingCatalogLookup.program
                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) d
                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt W)
                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (left i))
                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (right i))
                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                            (@List.nil.{0} Int)))))))
                                μ (ThreeSum.LightReportingCatalogLookup.time W n) fun (r : Int) (μ' : Nat → Int) =>
                                And (@Eq.{1} Int r (@Nat.cast.{0} Int instNatCastInt i)) (Light.Kept μ μ' work) := by
  exact @ThreeSum.LightReportingCatalogLookup.program_meets_sourceProof

#print axioms solution
