-- Prove2me | solution 1 for ThreeSum.LightCoverKeys.Procs.meets_with_masks
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:54:02.627294+00:00
-- url     : https://prove2.me/submissions/ffca1afb-b54a-43ef-89bf-ea82dbe5ef7a

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
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle14
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
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
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
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
import Theorems.Thm_ThreeSum_LightGlobalKeys_Procs_meets_with_masks
import Theorems.Thm_ThreeSum_LightLocalCoverInit_Procs_meets
import Theorems.Thm_ThreeSum_LightLocalCoverTables_Data_of_kept


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverMetadata
end ThreeSum.LightLocalCoverMetadata
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightLocalCoverTables
end ThreeSum.LightLocalCoverTables
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
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

































































































































end Light

end
end

section


/-! # Retained local-cover tables survive reuse of the returned free region -/

namespace ThreeSum.LightLocalCoverRetention

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMetadata

set_option maxHeartbeats 1000000

theorem base_le_nextFree (base h : ℕ) : base ≤ nextFree base h := by
  unfold nextFree scheduleMaps work matrixPtr hist1 hist0 raw1 raw0 maps bitPtr
    LightCoverGreedy.total
  omega

theorem table_ends_le (base h : ℕ) :
    maps base h+rows h*(2*(512*h)) ≤ nextFree base h ∧
    hist0 base h+rows h*localPrime h ≤ nextFree base h ∧
    hist1 base h+rows h*localPrime h ≤ nextFree base h ∧
    matrixPtr base h+rows h*cols h ≤ nextFree base h ∧
    candidates base h+scheduleSize h ≤ nextFree base h := by
  unfold nextFree scheduleMaps candidates work matrixPtr hist1 hist0 raw1 raw0 maps bitPtr
    LightCoverGreedy.total LightCoverGreedy.out
  omega

theorem data_of_kept {μ ν : ℕ → ℤ} {base h : ℕ}
    (H : Data μ h (maps base h) (hist0 base h) (hist1 base h) (matrixPtr base h))
    (K : Kept μ ν (nextFree base h)) :
    Data ν h (maps base h) (hist0 base h) (hist1 base h) (matrixPtr base h) := by
  obtain ⟨hm,hl,hr,hx,_⟩ := table_ends_le base h
  exact H.of_kept K hm hl hr hx

theorem rows_of_kept {μ ν : ℕ → ℤ} {base h : ℕ}
    (H : ScheduleRows μ h (scheduleMaps base h))
    (K : Kept μ ν (nextFree base h)) :
    ScheduleRows ν h (scheduleMaps base h) := by
  intro s hs i hi
  have hm := Nat.mul_le_mul_right (2*(512*h)) (show s+1 ≤ scheduleSize h by omega)
  simp only [Nat.add_mul,one_mul] at hm
  rw [K _ (by unfold nextFree; omega),K _ (by unfold nextFree; omega)]
  exact H s hs i hi

theorem indices_of_kept {μ ν : ℕ → ℤ} {base h : ℕ}
    (H : ∀ s : Occurrence h, μ (candidates base h+s.val) = (candidateAt h s : ℤ))
    (K : Kept μ ν (nextFree base h)) :
    ∀ s : Occurrence h, ν (candidates base h+s.val) = (candidateAt h s : ℤ) := by
  intro s
  have he := (table_ends_le base h).2.2.2.2
  rw [K _ (by have hs := s.isLt; omega)]
  exact H s

theorem header_of_kept {μ ν : ℕ → ℤ} {free h : ℕ}
    (H : Seg μ free (LightLocalCoverInit.values free h))
    (K : Kept μ ν (nextFree (LightLocalCoverInit.base free) h)) :
    Seg ν free (LightLocalCoverInit.values free h) := by
  have he : free+20 ≤ nextFree (LightLocalCoverInit.base free) h :=
    base_le_nextFree (LightLocalCoverInit.base free) h
  apply H.congr
  intro i hi
  have hi' : i < 20 := by
    simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,values] using hi
  exact K _ (by omega)




end ThreeSum.LightLocalCoverRetention

end

section


/-!
# From h to the original local cover and all global output keys

The fixed host obtains every key-constructor parameter from the header
written by the actual local-cover initializer. The original schedule,
candidate histograms, metadata, and input prefix remain available afterwards.
-/

namespace ThreeSum.LightCoverKeys

open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

























variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets_with_masks_sourceProof {pMain h J free : ℕ} {μ : ℕ → ℤ} (S : Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+J+11 ≤ lim.depth)
    (hspace : space free h J ≤ lim.space) (hword : (word h J : ℤ) ≤ lim.word) :
    Meets lim P pMain d [h,J,free] μ (time h J)
      (fun r ν => r=(keyHeader free h J : ℤ) ∧
        ν (keyHeader free h J)=((LightGlobalKeys.localCount h^J : ℕ) : ℤ) ∧
        Seg ν (keyHeader free h J+1) (globalKeys h J) ∧
        Seg ν free (LightLocalCoverInit.values free h) ∧
        Data ν h (maps (LightLocalCoverInit.base free) h)
          (hist0 (LightLocalCoverInit.base free) h) (hist1 (LightLocalCoverInit.base free) h)
          (matrixPtr (LightLocalCoverInit.base free) h) ∧
        ScheduleRows ν h (scheduleMaps (LightLocalCoverInit.base free) h) ∧
        (∀ s : Occurrence h, ν (candidates (LightLocalCoverInit.base free) h+s.val)=
          (candidateAt h s : ℤ)) ∧
        (∀ i < outputCount (512*h) h, ν (afterCover free h+i)=
          (LocalMaskGraph.maskAt (512*h) (2*h) i : ℤ)) ∧ Kept μ ν free) := by
  have hcspace : LightLocalCoverInit.space free h ≤ lim.space := (le_max_left _ _).trans hspace
  have hkspace : LightGlobalKeys.space (afterCover free h) h J ≤ lim.space :=
    (le_max_right _ _).trans hspace
  have hcword : (LightLocalCoverInit.word h : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_left _ _)).trans hword
  have hkword : (LightGlobalKeys.word h J : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_right _ _)).trans hword
  have hbaseNext : free+20 ≤ afterCover free h :=
    LightLocalCoverRetention.base_le_nextFree (LightLocalCoverInit.base free) h
  have hnextSpace : afterCover free h ≤ lim.space := by
    have hs : LightLocalKeyRow.space (LightGlobalKeys.scratch (afterCover free h) h)
        (512*h) (outputCount (512*h) h) ≤ lim.space :=
      (le_max_left _ _).trans hkspace
    unfold LightLocalKeyRow.space LightGlobalKeys.scratch at hs
    omega
  apply Meets.of_body S.main
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
            ((S.cover.meets (d := d + 1) hw (by omega) hcspace hcword) _
              (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (S.cover.meets (d := d + 1) hw (by omega) hcspace hcword) ?_ ?_ ?_
            ?_);
    (on_goal -1 =>
        first
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
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (on_goal -1 =>
        ((rintro next μ₁ ⟨hnext, hheader, hdata, hrows, hindices, hkeep₁⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have h0 : μ₁ free=(outputCount (512*h) h : ℤ) := by
    simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
      LightLocalCoverMetadata.values] using hheader 0 (by simp [LightLocalCoverInit.values,
      LightLocalParameters.values,LightLocalCounts.values,LightLocalCoverMetadata.values])
  have h6 : μ₁ (free+6)=(localPrime h : ℤ) := by
    simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
      LightLocalCoverMetadata.values] using hheader 6 (by simp [LightLocalCoverInit.values,
      LightLocalParameters.values,LightLocalCounts.values,LightLocalCoverMetadata.values])
  have h8 : μ₁ (free+8)=(512*h : ℤ) := by
    simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
      LightLocalCoverMetadata.values] using hheader 8 (by simp [LightLocalCoverInit.values,
      LightLocalParameters.values,LightLocalCounts.values,LightLocalCoverMetadata.values])
  have h9 : μ₁ (free+9)=(2*h : ℤ) := by
    simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
      LightLocalCoverMetadata.values] using hheader 9 (by simp [LightLocalCoverInit.values,
      LightLocalParameters.values,LightLocalCounts.values,LightLocalCoverMetadata.values])
  have h10 : μ₁ (free+10)=(scheduleSize h : ℤ) := by
    simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
      LightLocalCoverMetadata.values] using hheader 10 (by simp [LightLocalCoverInit.values,
      LightLocalParameters.values,LightLocalCounts.values,LightLocalCoverMetadata.values])
  have h12 : μ₁ (free+12)=(scheduleMaps (LightLocalCoverInit.base free) h : ℤ) := by
    simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
      LightLocalCoverMetadata.values] using hheader 12 (by simp [LightLocalCoverInit.values,
      LightLocalParameters.values,LightLocalCounts.values,LightLocalCoverMetadata.values])
  have hk := S.keys.meets_with_masks (d := d+1) (h := h) (J := J)
    (maps := scheduleMaps (LightLocalCoverInit.base free) h) (free := afterCover free h)
    hw (by omega) hkspace hkword le_rfl
    (fun j hj i hi => (hrows j hj i hi).1) (fun j hj i hi => (hrows j hj i hi).2)
  have haddress (i : ℕ) : ((free : ℤ)+(i : ℤ)).toNat=free+i := by omega
  have h6Read : μ₁ (((free : ℤ)+6).toNat)=(localPrime h : ℤ) := by
    rw [show ((free : ℤ)+6).toNat=free+6 by omega]
    exact h6
  have h8Read : μ₁ (((free : ℤ)+8).toNat)=(512*h : ℤ) := by
    rw [show ((free : ℤ)+8).toNat=free+8 by omega]
    exact h8
  have h9Read : μ₁ (((free : ℤ)+9).toNat)=(2*h : ℤ) := by
    rw [show ((free : ℤ)+9).toNat=free+9 by omega]
    exact h9
  have h10Read : μ₁ (((free : ℤ)+10).toNat)=(scheduleSize h : ℤ) := by
    rw [show ((free : ℤ)+10).toNat=free+10 by omega]
    exact h10
  have h12Read : μ₁ (((free : ℤ)+12).toNat)=(scheduleMaps (LightLocalCoverInit.base free) h : ℤ) := by
    rw [show ((free : ℤ)+12).toNat=free+12 by omega]
    exact h12
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
      | refine Light.Ends.callToThen (hk _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hk ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h0,
                h6Read, h8Read, h9Read, h10Read, h12Read, hnext, afterCover]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [h0, h6Read, h8Read, h9Read, h10Read, h12Read, hnext,
                afterCover] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, h0, h6Read, h8Read, h9Read,
                h10Read, h12Read, hnext, afterCover] <;>
              omega)));
    (on_goal -1 =>
        ((rintro result μ₂ ⟨hr, hcount, hkeys, hmasks, hkeep₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  refine ⟨hr,hcount,hkeys,LightLocalCoverRetention.header_of_kept hheader hkeep₂,
    LightLocalCoverRetention.data_of_kept hdata hkeep₂,
    LightLocalCoverRetention.rows_of_kept hrows hkeep₂,
    LightLocalCoverRetention.indices_of_kept hindices hkeep₂,hmasks,?_⟩
  intro a ha
  exact (hkeep₂ a (by omega)).trans (hkeep₁ a ha)
















































end ThreeSum.LightCoverKeys

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain h J free : Nat} {μ : Nat → Int}
  (S : ThreeSum.LightCoverKeys.Procs P pMain),
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
            J)
          (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
        lim.depth →
      @LE.le.{0} Nat instLENat (ThreeSum.LightCoverKeys.space free h J) lim.space →
        @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightCoverKeys.word h J)) lim.word →
          Light.Meets lim P pMain d
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt h)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt J)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt free) (@List.nil.{0} Int))))
            μ (ThreeSum.LightCoverKeys.time h J) fun (r : Int) (ν : Nat → Int) =>
            And (@Eq.{1} Int r (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightCoverKeys.keyHeader free h J)))
              (And
                (@Eq.{1} Int (ν (ThreeSum.LightCoverKeys.keyHeader free h J))
                  (@Nat.cast.{0} Int instNatCastInt
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                      (ThreeSum.LightGlobalKeys.localCount h) J)))
                (And
                  (Light.Seg ν
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (ThreeSum.LightCoverKeys.keyHeader free h J)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (ThreeSum.GlobalKeyEnumeration.globalKeys h J))
                  (And (Light.Seg ν free (ThreeSum.LightLocalCoverInit.values free h))
                    (And
                      (ThreeSum.LightLocalCoverTables.Data ν h
                        (ThreeSum.LightLocalCoverLayout.maps (ThreeSum.LightLocalCoverInit.base free) h)
                        (ThreeSum.LightLocalCoverLayout.hist0 (ThreeSum.LightLocalCoverInit.base free) h)
                        (ThreeSum.LightLocalCoverLayout.hist1 (ThreeSum.LightLocalCoverInit.base free) h)
                        (ThreeSum.LightLocalCoverLayout.matrixPtr (ThreeSum.LightLocalCoverInit.base free) h))
                      (And
                        (ThreeSum.LightLocalCoverTables.ScheduleRows ν h
                          (ThreeSum.LightLocalCoverLayout.scheduleMaps (ThreeSum.LightLocalCoverInit.base free) h))
                        (And
                          (∀ (s : ThreeSum.GlobalEncoding.Occurrence h),
                            @Eq.{1} Int
                              (ν
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (ThreeSum.LightLocalCoverLayout.candidates (ThreeSum.LightLocalCoverInit.base free) h)
                                  (@Fin.val (ThreeSum.GlobalEncoding.scheduleSize h) s)))
                              (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightLocalCoverSchedule.candidateAt h s)))
                          (And
                            (∀ (i : Nat),
                              @LT.lt.{0} Nat instLTNat i
                                  (ThreeSum.LocalCoverBounds.outputCount
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                    h) →
                                @Eq.{1} Int
                                  (ν
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (ThreeSum.LightCoverKeys.afterCover free h) i))
                                  (@Nat.cast.{0} Int instNatCastInt
                                    (ThreeSum.LocalMaskGraph.maskAt
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)
                                      i)))
                            (Light.Kept μ ν free)))))))) := by
  exact @ThreeSum.LightCoverKeys.Procs.meets_with_masks_sourceProof

#print axioms solution
