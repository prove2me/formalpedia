-- Prove2me | solution 1 for ThreeSum.LightBandRawAColor.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:41:36.825895+00:00
-- url     : https://prove2.me/submissions/de49a042-e70d-42dc-be25-dacb457253e1

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
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
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
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
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
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
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
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bitwise
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
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.DeriveFintype
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
import Theorems.Thm_ThreeSum_LightBandPreprocessing_Represents_keep
import Theorems.Thm_ThreeSum_LightBandRawACatalog_Procs_meets
import Theorems.Thm_ThreeSum_LightBandRawAColor_tables_keep
import Theorems.Thm_ThreeSum_LightColorBands_Procs_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress

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












end ThreeSum.LightBandEnumeration

end

section


/-!
# The exact physical band-owner record order

There is one four-cell record for every owner-table cell, in BC, AB, AC
rectangle order. A zero flag is a lookup miss. Successful records retain
their physical owner slot even when several owners produce the same triple.
-/

namespace ThreeSum.BandCandidateRows

open BandEnumeration

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000



















































theorem rect_length (m n : ℕ) (F : ℕ → ℕ → Record) : (rect m n F).length=m*n := by
  simp [rect,List.length_flatMap]

theorem records_length (A B C : Family) :
    (records A B C).length=LightBandEnumeration.count A.size B.size C.size := by
  simp only [records,List.length_append,rect_length,LightBandEnumeration.count]
  omega


















































































































































end ThreeSum.BandCandidateRows

end

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



































































end ThreeSum.ColorClassLists

end

section


/-!
# All actual flagged band-owner records

The fixed program reads the three retained rectangular lookup tables and
writes one four-cell record for each cell, in the same BC, AB, AC order.
The record position is its permanent owner-slot identity.
-/

namespace ThreeSum.LightBandCandidates

open Light BandEnumeration BandCandidateRows

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000








































variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {src dst : ℕ}














































































































































theorem time_bound (a b c : ℕ) :
    time a b c ≤ 1000*(LightBandEnumeration.count a b c+a+b+c+1) := by
  unfold time LightBandCandidatesTable.time LightBandCandidatesRow.time
    LightBandCandidatesCell.time LightBandEnumeration.count
  nlinarith

end ThreeSum.LightBandCandidates

end

section


/-!
# The actual flattened A-incidence catalog

The loop reads each four-cell owner record once. Successful records append
only their actual truncated A band. Parallel value, owner-slot, and sorted
position arrays are packed using capacity g times the owner count.
-/

namespace ThreeSum.LightBandRawA

open Light BandCandidateRows BandRawA

set_option maxHeartbeats 2200000
set_option maxRecDepth 8000







































variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {records src n g vals : ℕ} {rs : List Record} {f : ℕ → ℤ}




















































































































































theorem time_bound (N g : ℕ) : time N g ≤ 1000*(N+1)*(g+1) := by
  unfold time LightBandRawAStep.time LightBandRawARow.time copyTime fillTime
  nlinarith

end ThreeSum.LightBandRawA

end

section


/-!
# Read the retained headers, build owner records, and extract A incidences

The fixed program reads the actual sorted-A length and all three actual
band counts from the retained headers. It constructs the exact physical
BC, AB, AC records, then copies their flagged A bands into the three packed
value/owner/position arrays. No supplied enumeration or hidden input list
is used by either machine loop.
-/

namespace ThreeSum.LightBandRawACatalog

open Light BandEnumeration BandCandidateRows BandRawA

set_option maxHeartbeats 2100000
set_option maxRecDepth 8000


























variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {tables rec src headerA headerB headerC nA nB nC g vals : ℕ} {f : ℕ → ℤ}




















































































































theorem time_bound (a b c g : ℕ) :
    time a b c g ≤ 3000*(LightBandEnumeration.count a b c+a+b+c+1)*(g+1) := by
  have hc := LightBandCandidates.time_bound a b c
  have hr := LightBandRawA.time_bound (LightBandEnumeration.count a b c) g
  unfold time
  nlinarith

end ThreeSum.LightBandRawACatalog

end

section


/-!
# Original input to the retained owner and A-incidence catalog

The selected index coloring, class extraction, normalization, endpoint
construction, three rectangular owner tables, four-cell owner records, and
packed A-incidence rows are all executed by this fixed program. The rows
retain physical owner identities and sorted-array coordinates. Membership
in the original color classes is retained separately by `Represents`.
-/

namespace ThreeSum.LightBandRawAColor

open Light BandPartition BandCandidateRows BandRawA ColorClassLists

set_option maxHeartbeats 2400000
set_option maxRecDepth 11000




































































variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets_sourceProof
    {pMain src n W colors dst0 dst1 dst2 g av ae bv be cv ce work rec vals U : ℕ}
    {μ : ℕ → ℤ} (R : Procs P pMain) (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : n ≤ 2^W) (hg : 0 < g)
    (hsrc : src+n ≤ colors) (hcolors : colors+n ≤ dst0)
    (h0 : dst0+n+1 ≤ dst1) (h1 : dst1+n+1 ≤ dst2) (h2 : dst2+n+1 ≤ av)
    (hav : av+n ≤ ae) (hae : ae+2+2*n ≤ bv)
    (hbv : bv+n ≤ be) (hbe : be+2+2*n ≤ cv)
    (hcv : cv+n ≤ ce) (hce : ce+2+2*n ≤ work)
    (htable : work+ColorBandBounds.count n g ≤ rec)
    (hrec : rec+4*ColorBandBounds.count n g ≤ vals)
    (hspace : space work vals W n g ≤ lim.space)
    (hword : (word W n g U : ℤ) ≤ lim.word) (hd : d+depth W n g ≤ lim.depth)
    (hread : Seg μ src (List.ofFn x)) (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    Meets lim P pMain d [src,n,W,p.1.1.val,p.1.2.val,(p.2 (false,false)).val,
      (p.2 (false,true)).val,(p.2 (true,false)).val,(p.2 (true,true)).val,
      colors,dst0,dst1,dst2,g,av,ae,bv,be,cv,ce,work,rec,vals] μ (time W n g)
      (fun r ν => Output ν av ae bv be cv ce work rec vals g hg
        (classList p x 0 1) (classList p x 1 1) (classList p x 2 (-1)) r ∧
          Kept μ ν colors) := by
  have hcSpace := (Nat.le_max_left (LightColorBands.space work W n g)
    (LightBandRawA.space vals (ColorBandBounds.count n g) g)).trans hspace
  have hrSpace := (Nat.le_max_right (LightColorBands.space work W n g)
    (LightBandRawA.space vals (ColorBandBounds.count n g) g)).trans hspace
  have hcWord : (LightColorBands.word W n g U : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show LightColorBands.word W n g U ≤ word W n g U by
      unfold word; omega)).trans hword
  have hcDepth : d+1+LightColorBands.depth W n g ≤ lim.depth := by
    unfold depth at hd; omega
  have hrDepth : d+1+3 < lim.depth := by unfold depth at hd; omega
  have len0 := length_classList_le p x 0 1
  have len1 := length_classList_le p x 1 1
  have len2 := length_classList_le p x 2 (-1)
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
            ((R.color.meets (d := d + 1) p x hw hn hg hsrc hcolors h0 h1 h2 hav
                hae hbv hbe hcv hce hcSpace hcWord hcDepth hread hbound)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (R.color.meets (d := d + 1) p x hw hn hg hsrc hcolors h0 h1 h2 hav hae
              hbv hbe hcv hce hcSpace hcWord hcDepth hread hbound)
            ?_ ?_ ?_ ?_);
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
        ((rintro colorResult ν₁ ⟨hout, hkeepColor⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  obtain ⟨A,hsA,B,hsB,C,hsC,hcolorResult,hrepA,hrepB,hrepC,htables⟩ := hout
  let aFamily := family (fun i => A.getD i 0) A.length g hg (LightSortedBands.getD_strict hsA)
  let bFamily := family (fun i => B.getD i 0) B.length g hg (LightSortedBands.getD_strict hsB)
  let cFamily := family (fun i => C.getD i 0) C.length g hg (LightSortedBands.getD_strict hsC)
  have hnA : A.length ≤ n := hrepA.2.1.trans len0
  have hnB : B.length ≤ n := hrepB.2.1.trans len1
  have hnC : C.length ≤ n := hrepC.2.1.trans len2
  have ha : aFamily.size ≤ size n g := size_mono hnA
  have hb : bFamily.size ≤ size n g := size_mono hnB
  have hc : cFamily.size ≤ size n g := size_mono hnC
  have hcount : LightBandEnumeration.count aFamily.size bFamily.size cFamily.size ≤
      ColorBandBounds.count n g := by
    have hh := LightBandEnumeration.count_mono ha hb hc
    have heq : LightBandEnumeration.count (size n g) (size n g) (size n g) =
        ColorBandBounds.count n g := by unfold LightBandEnumeration.count ColorBandBounds.count; ring
    rwa [heq] at hh
  have hcatSpace : LightBandRawACatalog.space vals aFamily.size bFamily.size cFamily.size g ≤
      lim.space := by
    have hm := Nat.mul_le_mul_left g hcount
    unfold LightBandRawACatalog.space LightBandRawA.space LightBandRawA.positionBase
      LightBandRawA.ownerBase LightBandRawA.capacity at hrSpace ⊢
    omega
  have hcatWord : (LightBandRawACatalog.word A.length aFamily.size bFamily.size cFamily.size g : ℤ) ≤
      lim.word := by
    have hh := LightBandEnumeration.count_mono ha hb hc
    apply (Int.ofNat_le.mpr (show LightBandRawACatalog.word A.length aFamily.size bFamily.size
        cFamily.size g ≤ word W n g U by
      unfold word LightBandRawACatalog.word LightBandCandidates.word LightBandRawA.word
      omega)).trans hword
  have hcatTime : LightBandRawACatalog.time aFamily.size bFamily.size cFamily.size g ≤
      catalogTime n g := by
    apply (LightBandRawACatalog.time_bound _ _ _ _).trans
    unfold catalogTime
    exact Nat.mul_le_mul_right (g+1) (Nat.mul_le_mul_left 3000 (by omega))
  have hsource : ∀ j < A.length, ν₁ (av+j)=A.getD j 0 := by
    intro j hj
    exact hrepA.1.getD hj 0
  have hcat := R.catalog.meets (d := d+1) (tables := work) (rec := rec) (src := av)
    (headerA := ae) (headerB := be) (headerC := ce) (vals := vals)
    aFamily bFamily cFamily rfl hw hrDepth hg (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hcatSpace hcatWord
    hrepA.2.2.2 hrepB.2.2.2 hrepC.2.2.2 htables hsource
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
          Light.Ends.callToThen ((hcat.mono_time hcatTime) _ (by omega)) ?_ ?_ ?_
            ?_
      | refine Light.Ends.callToThen (hcat.mono_time hcatTime) ?_ ?_ ?_ ?_);
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
        ((rintro result ν₂ ⟨hresult, hrecords, hstored, hkeepCatalog⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  refine ⟨⟨A,hsA,B,hsB,C,hsC,hresult,
    hrepA.keep hkeepCatalog (by omega) (by omega),
    hrepB.keep hkeepCatalog (by omega) (by omega),
    hrepC.keep hkeepCatalog (by omega) (by omega),
    tables_keep (A := aFamily) (B := bFamily) (C := cFamily)
      htables hkeepCatalog (by omega),hrecords,?_⟩,?_⟩
  · simpa only [sortedRecords,records_length] using hstored
  · intro a ha'
    change ν₂ a=μ a
    exact (hkeepCatalog a (by omega)).trans (hkeepColor a ha')
































































end ThreeSum.LightBandRawAColor

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program}
  {d pMain src n W colors dst0 dst1 dst2 g av ae bv be cv ce work rec vals U : Nat} {μ : Nat → Int}
  (R : ThreeSum.LightBandRawAColor.Procs P pMain) (p : ThreeSum.Coloring.Parameter W) (x : Fin n → Int),
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
                              @LE.le.{0} Nat instLENat
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
                                    (ThreeSum.ColorBandBounds.count n g))
                                  rec →
                                @LE.le.{0} Nat instLENat
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rec
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                        (ThreeSum.ColorBandBounds.count n g)))
                                    vals →
                                  @LE.le.{0} Nat instLENat (ThreeSum.LightBandRawAColor.space work vals W n g)
                                      lim.space →
                                    @LE.le.{0} Int Int.instLEInt
                                        (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightBandRawAColor.word W n g U))
                                        lim.word →
                                      @LE.le.{0} Nat instLENat
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                                            (ThreeSum.LightBandRawAColor.depth W n g))
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
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                                (instOfNatNat (nat_lit 3)))
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
                                                                    p
                                                                    (@Prod.mk.{0, 0} Bool Bool Bool.true Bool.false))))
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
                                                                      p
                                                                      (@Prod.mk.{0, 0} Bool Bool Bool.true Bool.true))))
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
                                                                                    (@Nat.cast.{0} Int instNatCastInt
                                                                                      cv)
                                                                                    (@List.cons.{0} Int
                                                                                      (@Nat.cast.{0} Int instNatCastInt
                                                                                        ce)
                                                                                      (@List.cons.{0} Int
                                                                                        (@Nat.cast.{0} Int
                                                                                          instNatCastInt work)
                                                                                        (@List.cons.{0} Int
                                                                                          (@Nat.cast.{0} Int
                                                                                            instNatCastInt rec)
                                                                                          (@List.cons.{0} Int
                                                                                            (@Nat.cast.{0} Int
                                                                                              instNatCastInt vals)
                                                                                            (@List.nil.{0}
                                                                                              Int))))))))))))))))))))))))
                                              μ (ThreeSum.LightBandRawAColor.time W n g)
                                              fun (r : Int) (ν : Nat → Int) =>
                                              And
                                                (ThreeSum.LightBandRawAColor.Output ν av ae bv be cv ce work rec vals g
                                                  hg
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
  exact @ThreeSum.LightBandRawAColor.Procs.meets_sourceProof

#print axioms solution
