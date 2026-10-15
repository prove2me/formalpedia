-- Prove2me | solution 1 for ThreeSum.LightBlockSourceHashes.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:11:32.492392+00:00
-- url     : https://prove2.me/submissions/f90e0706-a9df-4332-9ee9-722e18cafc63

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
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
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
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
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
import Theorems.Thm_ThreeSum_BlockCoefficientRows_rows_flat
import Theorems.Thm_ThreeSum_LightBlockCoefficients_meets
import Theorems.Thm_ThreeSum_LightMaskHashes_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds

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
# Constructing the positional one-hot coefficient arrays

The program reads one map occurrence per block. It copies both symbol rows
of that map and multiplies them by the block's radix power. The powers are
built internally. All original map and occurrence data are preserved.
-/

namespace ThreeSum.LightBlockCoefficients

open Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

variable {lim : Limits} {P : Program}

































theorem row_end_le {J L j : ℕ} (hj : j < J) : j*L+L ≤ J*L := by
  calc
    j*L+L = (j+1)*L := by ring
    _ ≤ J*L := Nat.mul_le_mul_right L (by omega)















































































































































































end ThreeSum.LightBlockCoefficients

end

section


/-!
# Reading constructed block coefficients in the flat mask order

The imperative coefficient constructor writes rows. The mask evaluator reads
one flat array. These lemmas identify the two layouts, including empty ground
sets, and specialize them to the unchanged schedule-occurrence encoding.
-/

namespace ThreeSum.BlockCoefficientRows

open BlockRows BlockIndex BlockEncoding GlobalEncoding LocalCoverBounds




























theorem flat_le {J L p U M : ℕ} {sel : ℕ → ℕ} {w : ℕ → ℕ → ℕ}
    (hp : 1 ≤ p) (hsel : ∀ j < J, sel j < M)
    (hbound : ∀ s < M, ∀ i < L, w s i ≤ U) {i : ℕ} (hi : i < J*L) :
    flat J L p sel w i ≤ p^J*U := by
  let c := (coordEquiv J L).symm ⟨i,hi⟩
  change (if h : i < J*L then _ else 0) ≤ _
  rw [dif_pos hi]
  exact Nat.mul_le_mul (Nat.pow_le_pow_right hp (Nat.le_of_lt c.1.isLt))
    (hbound _ (hsel _ c.1.isLt) _ c.2.isLt)




















































end ThreeSum.BlockCoefficientRows

end

section


/-!
# Constructing both raw endpoint arrays from selected block maps

The program constructs radix-weighted coefficient rows itself, then hashes
each stored subset in both orientations. Both endpoint arrays and the
coefficient rows are retained. The final specialization identifies the
results with the original block encoding, preserving occurrence indices.
-/

namespace ThreeSum.LightBlockSourceHashes

open Light BlockCoefficientRows

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000





























variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets_sourceProof {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {J L p occ maps coeff0 coeff1 masks rawLeft rawRight n work U M : ℕ}
    (sel mask : ℕ → ℕ) (w0 w1 : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 1 ≤ p)
    (hd : d+J*L+2 ≤ lim.depth) (hspace : space work J L ≤ lim.space)
    (hocc : occ+J ≤ coeff0) (hmaps : maps+2*L*M ≤ coeff0)
    (hmasks : masks+n ≤ coeff0) (hc0 : coeff0+J*L ≤ coeff1)
    (hc1 : coeff1+J*L ≤ rawLeft) (hleft : rawLeft+n ≤ rawRight)
    (hright : rawRight+n ≤ work) (hword : (word J L p U : ℤ) ≤ lim.word)
    (hsel : ∀ j < J, sel j < M)
    (hselRead : ∀ j < J, μ (occ+j) = (sel j : ℤ))
    (hread0 : ∀ s < M, ∀ i < L, μ (maps+2*L*s+i) = (w0 s i : ℤ))
    (hread1 : ∀ s < M, ∀ i < L, μ (maps+2*L*s+L+i) = (w1 s i : ℤ))
    (hbound0 : ∀ s < M, ∀ i < L, w0 s i ≤ U)
    (hbound1 : ∀ s < M, ∀ i < L, w1 s i ≤ U)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^(J*L)) :
    Meets lim P pMain d [J,L,p,occ,maps,coeff0,coeff1,masks,rawLeft,rawRight,n,work]
      μ (time J L n) (fun _ ν =>
        (∀ i < n, ν (rawLeft+i) =
          (OneHotMask.eval (flat J L p sel w0) (flat J L p sel w1) (J*L) (mask i) : ℤ)) ∧
        (∀ i < n, ν (rawRight+i) =
          (OneHotMask.eval (flat J L p sel w1) (flat J L p sel w0) (J*L) (mask i) : ℤ)) ∧
        LightBlockCoefficients.Rows ν coeff0 coeff1 L p sel w0 w1 J ∧ Kept μ ν coeff0) := by
  have hsc : work+(J+1) ≤ lim.space :=
    (Nat.add_le_add_left (le_max_left _ _) work).trans hspace
  have hsh : work+(J*L+1) ≤ lim.space :=
    (Nat.add_le_add_left (le_max_right _ _) work).trans hspace
  have hcw : (LightBlockCoefficients.word J p U : ℤ) ≤ lim.word := by
    have hh : LightBlockCoefficients.word J p U ≤ word J L p U := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hhw : (LightOneHot.word (J*L) (p^J*U) : ℤ) ≤ lim.word := by
    have hh : LightOneHot.word (J*L) (p^J*U) ≤ word J L p U := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwidth : (J : ℤ)*(L : ℤ) ≤ lim.word := by
    have hh : J*L ≤ lim.space := by omega
    exact (by exact_mod_cast hh : (J : ℤ)*(L : ℤ) ≤ lim.space).trans hw
  have hb0 : ∀ i < J*L, flat J L p sel w0 i ≤ p^J*U :=
    fun _ hi => flat_le hp hsel hbound0 hi
  have hb1 : ∀ i < J*L, flat J L p sel w1 i ≤ p^J*U :=
    fun _ hi => flat_le hp hsel hbound1 hi
  apply Meets.of_body S.main
  unfold body time
  have hc := LightBlockCoefficients.meets (d := d+1) (μ := μ)
    (J := J) (L := L) (p := p) (occ := occ) (maps := maps)
    (dst0 := coeff0) (dst1 := coeff1) (work := work) (U := U) (M := M)
    S.coefficients S.powers S.scale sel w0 w1 hw hp hocc hmaps hc0 (by omega)
    hsc hcw (by omega) hsel hselRead hread0 hread1 hbound0 hbound1
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
                LightBlockCoefficients.time, LightBlockCoefficients.roundTime,
                LightMaskHashes.time, LightOneHot.time, LightScaleArray.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightBlockCoefficients.time, LightBlockCoefficients.roundTime,
                LightMaskHashes.time, LightOneHot.time, LightScaleArray.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, LightBlockCoefficients.time,
                LightBlockCoefficients.roundTime, LightMaskHashes.time,
                LightOneHot.time, LightScaleArray.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro r μ₁ ⟨rows, kept₁, _⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  obtain ⟨rows0,rows1⟩ := rows_flat rows
  have masks₁ : ∀ i < n, μ₁ (masks+i) = (mask i : ℤ) := by
    intro i hi
    exact (kept₁ _ (by omega)).trans (hmaskRead i hi)
  have hl := LightMaskHashes.meets (d := d+1) (μ := μ₁)
    (L := J*L) (masks := masks) (dst := rawLeft) (n := n)
    (src0 := coeff0) (src1 := coeff1) (work := work) (U := p^J*U)
    S.hashes S.powers S.onehot mask (flat J L p sel w0) (flat J L p sel w1)
    hw (by omega) hsh (by omega) (by omega) hc1 (by omega) hhw masks₁ hmaskLt
    rows0 rows1 hb0 hb1
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
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightBlockCoefficients.time, LightBlockCoefficients.roundTime,
                LightMaskHashes.time, LightOneHot.time, LightScaleArray.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightBlockCoefficients.time, LightBlockCoefficients.roundTime,
                LightMaskHashes.time, LightOneHot.time, LightScaleArray.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, LightBlockCoefficients.time,
                LightBlockCoefficients.roundTime, LightMaskHashes.time,
                LightOneHot.time, LightScaleArray.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro r μ₂ ⟨leftValues, _, kept₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have masks₂ : ∀ i < n, μ₂ (masks+i) = (mask i : ℤ) := by
    intro i hi
    exact (kept₂ _ ⟨by omega,Or.inl (by omega)⟩).trans (masks₁ i hi)
  have rows0₂ : ∀ i < J*L, μ₂ (coeff0+i) = (flat J L p sel w0 i : ℤ) := by
    intro i hi
    exact (kept₂ _ ⟨by omega,Or.inl (by omega)⟩).trans (rows0 i hi)
  have rows1₂ : ∀ i < J*L, μ₂ (coeff1+i) = (flat J L p sel w1 i : ℤ) := by
    intro i hi
    exact (kept₂ _ ⟨by omega,Or.inl (by omega)⟩).trans (rows1 i hi)
  have hr := LightMaskHashes.meets (d := d+1) (μ := μ₂)
    (L := J*L) (masks := masks) (dst := rawRight) (n := n)
    (src0 := coeff1) (src1 := coeff0) (work := work) (U := p^J*U)
    S.hashes S.powers S.onehot mask (flat J L p sel w1) (flat J L p sel w0)
    hw (by omega) hsh (by omega) (by omega) (by omega) hright hhw masks₂ hmaskLt
    rows1₂ rows0₂ hb1 hb0
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
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightBlockCoefficients.time, LightBlockCoefficients.roundTime,
                LightMaskHashes.time, LightOneHot.time, LightScaleArray.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightBlockCoefficients.time, LightBlockCoefficients.roundTime,
                LightMaskHashes.time, LightOneHot.time, LightScaleArray.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, LightBlockCoefficients.time,
                LightBlockCoefficients.roundTime, LightMaskHashes.time,
                LightOneHot.time, LightScaleArray.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro r μ₃ ⟨rightValues, _, kept₃⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  refine ⟨?_,rightValues,?_,?_⟩
  · intro i hi
    exact (kept₃ _ ⟨by omega,Or.inl (by omega)⟩).trans (leftValues i hi)
  · intro a ha i hi
    have he := LightBlockCoefficients.row_end_le (L := L) ha
    constructor
    · exact (kept₃ _ ⟨by omega,Or.inl (by omega)⟩).trans
        ((kept₂ _ ⟨by omega,Or.inl (by omega)⟩).trans (rows a ha i hi).1)
    · exact (kept₃ _ ⟨by omega,Or.inl (by omega)⟩).trans
        ((kept₂ _ ⟨by omega,Or.inl (by omega)⟩).trans (rows a ha i hi).2)
  · intro a ha
    exact (kept₃ _ ⟨by omega,Or.inl (by omega)⟩).trans
      ((kept₂ _ ⟨by omega,Or.inl (by omega)⟩).trans (kept₁ a ha))





























































end ThreeSum.LightBlockSourceHashes

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (S : ThreeSum.LightBlockSourceHashes.Procs P pMain)
  {μ : Nat → Int} {J L p occ maps coeff0 coeff1 masks rawLeft rawRight n work U M : Nat} (sel mask : Nat → Nat)
  (w0 w1 : Nat → Nat → Nat),
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) p →
      @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J L))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          lim.depth →
        @LE.le.{0} Nat instLENat (ThreeSum.LightBlockSourceHashes.space work J L) lim.space →
          @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) occ J) coeff0 →
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)
                    M))
                coeff0 →
              @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) masks n)
                  coeff0 →
                @LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) coeff0
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J L))
                    coeff1 →
                  @LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) coeff1
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J L))
                      rawLeft →
                    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rawLeft n)
                        rawRight →
                      @LE.le.{0} Nat instLENat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rawRight n) work →
                        @LE.le.{0} Int Int.instLEInt
                            (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightBlockSourceHashes.word J L p U)) lim.word →
                          (∀ (j : Nat), @LT.lt.{0} Nat instLTNat j J → @LT.lt.{0} Nat instLTNat (sel j) M) →
                            (∀ (j : Nat),
                                @LT.lt.{0} Nat instLTNat j J →
                                  @Eq.{1} Int
                                    (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) occ j))
                                    (@Nat.cast.{0} Int instNatCastInt (sel j))) →
                              (∀ (s : Nat),
                                  @LT.lt.{0} Nat instLTNat s M →
                                    ∀ (i : Nat),
                                      @LT.lt.{0} Nat instLTNat i L →
                                        @Eq.{1} Int
                                          (μ
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)
                                                  s))
                                              i))
                                          (@Nat.cast.{0} Int instNatCastInt (w0 s i))) →
                                (∀ (s : Nat),
                                    @LT.lt.{0} Nat instLTNat s M →
                                      ∀ (i : Nat),
                                        @LT.lt.{0} Nat instLTNat i L →
                                          @Eq.{1} Int
                                            (μ
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)
                                                      s))
                                                  L)
                                                i))
                                            (@Nat.cast.{0} Int instNatCastInt (w1 s i))) →
                                  (∀ (s : Nat),
                                      @LT.lt.{0} Nat instLTNat s M →
                                        ∀ (i : Nat),
                                          @LT.lt.{0} Nat instLTNat i L → @LE.le.{0} Nat instLENat (w0 s i) U) →
                                    (∀ (s : Nat),
                                        @LT.lt.{0} Nat instLTNat s M →
                                          ∀ (i : Nat),
                                            @LT.lt.{0} Nat instLTNat i L → @LE.le.{0} Nat instLENat (w1 s i) U) →
                                      (∀ (i : Nat),
                                          @LT.lt.{0} Nat instLTNat i n →
                                            @Eq.{1} Int
                                              (μ
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) masks
                                                  i))
                                              (@Nat.cast.{0} Int instNatCastInt (mask i))) →
                                        (∀ (i : Nat),
                                            @LT.lt.{0} Nat instLTNat i n →
                                              @LT.lt.{0} Nat instLTNat (mask i)
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                                    L))) →
                                          Light.Meets lim P pMain d
                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt J)
                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt p)
                                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt occ)
                                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt maps)
                                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt coeff0)
                                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt coeff1)
                                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt masks)
                                                            (@List.cons.{0} Int
                                                              (@Nat.cast.{0} Int instNatCastInt rawLeft)
                                                              (@List.cons.{0} Int
                                                                (@Nat.cast.{0} Int instNatCastInt rawRight)
                                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
                                                                  (@List.cons.{0} Int
                                                                    (@Nat.cast.{0} Int instNatCastInt work)
                                                                    (@List.nil.{0} Int)))))))))))))
                                            μ (ThreeSum.LightBlockSourceHashes.time J L n)
                                            fun (x : Int) (ν : Nat → Int) =>
                                            And
                                              (∀ (i : Nat),
                                                @LT.lt.{0} Nat instLTNat i n →
                                                  @Eq.{1} Int
                                                    (ν
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        rawLeft i))
                                                    (@Nat.cast.{0} Int instNatCastInt
                                                      (ThreeSum.OneHotMask.eval
                                                        (ThreeSum.BlockCoefficientRows.flat J L p sel w0)
                                                        (ThreeSum.BlockCoefficientRows.flat J L p sel w1)
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          J L)
                                                        (mask i))))
                                              (And
                                                (∀ (i : Nat),
                                                  @LT.lt.{0} Nat instLTNat i n →
                                                    @Eq.{1} Int
                                                      (ν
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          rawRight i))
                                                      (@Nat.cast.{0} Int instNatCastInt
                                                        (ThreeSum.OneHotMask.eval
                                                          (ThreeSum.BlockCoefficientRows.flat J L p sel w1)
                                                          (ThreeSum.BlockCoefficientRows.flat J L p sel w0)
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat) J L)
                                                          (mask i))))
                                                (And
                                                  (ThreeSum.LightBlockCoefficients.Rows ν coeff0 coeff1 L p sel w0 w1 J)
                                                  (Light.Kept μ ν coeff0))) := by
  exact @ThreeSum.LightBlockSourceHashes.Procs.meets_sourceProof

#print axioms solution
