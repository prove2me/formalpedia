-- Prove2me | solution 1 for ThreeSum.LightGlobalKeys.Procs.meets_with_masks
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:31:40.530976+00:00
-- url     : https://prove2.me/submissions/3b6c36df-82fe-49ef-8efd-edbe957a3039

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
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle11
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
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
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
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
import Theorems.Thm_ThreeSum_GlobalKeyEnumeration_rawOutput_abs_le
import Theorems.Thm_ThreeSum_LightLocalKeys_Procs_meets
import Theorems.Thm_ThreeSum_LightRadixKeys_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_meets
import Theorems.Thm_ThreeSum_LocalKeyArraySemantics_seg_flatMap_rows
import Theorems.Thm_ThreeSum_OneHotMask_eval_maskOf


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.OneHotMask
end ThreeSum.OneHotMask
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

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
# Evaluating a one-hot hash from a subset mask

The executable recursion examines exactly one bit per level using a cached
power of two.  Its result is the sum of the selected symbol coefficients,
and is connected here to the raw hashes used by the global encoding.
-/

namespace ThreeSum.OneHotMask

open Finset SubsetAddress LocalHashMoments
open scoped BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

























































@[simp] theorem extend_fin {L : ℕ} (f : Fin L → ℕ) (i : Fin L) :
    extend f i.val = f i := by simp [extend, i.isLt]

@[simp] theorem mem_natPositions {L : ℕ} (s : Finset (Fin L)) (i : Fin L) :
    i.val ∈ natPositions s ↔ i ∈ s := by
  simp only [natPositions, mem_map]
  constructor
  · rintro ⟨a,ha,he⟩
    have hai : a = i := Fin.ext he
    simpa only [hai] using ha
  · intro hi
    exact ⟨i,hi,rfl⟩

theorem eval_subsetMask {L : ℕ} (s : Finset (Fin L)) (w0 w1 : Fin L → ℕ) :
    eval (extend w0) (extend w1) L (subsetMask s) =
      ∑ i : Fin L, if i ∈ s then w1 i else w0 i := by
  rw [subsetMask, eval_maskOf _ (natPositions_subset s), Finset.sum_range]
  apply sum_congr rfl
  intro i _
  simp only [extend_fin, mem_natPositions]























end ThreeSum.OneHotMask

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


















































@[simp] theorem mapRow_fin {h : ℕ} (b : Bool) (s : Occurrence h) (i : Fin (512*h)) :
    mapRow h b s.val i.val = (mapAt h s (i,b)).val := by
  simp only [mapRow,s.isLt,dite_true,OneHotMask.extend_fin]





theorem mapRow_le {h : ℕ} (b : Bool) {s i : ℕ}
    (hs : s < scheduleSize h) (hi : i < 512*h) : mapRow h b s i ≤ localPrime h := by
  rw [mapRow_fin b ⟨s,hs⟩ ⟨i,hi⟩]
  exact Nat.le_of_lt (ZMod.val_lt _)



























end ThreeSum.BlockCoefficientRows

end

section


/-!
# Concrete integer indices for the local disjoint-subset graph

The finite list is the already checked layer-mask enumeration. Its Boolean
coordinate rows make disjointness an ordinary zero Boolean inner product.
-/

namespace ThreeSum.LocalMaskGraph

open Finset SubsetAddress MaskDecode
open scoped BigOperators












theorem maskAt_spec {L h i : ℕ} (hi : i < vertexCount L h) :
    IsMask L h (maskAt L h i) := (mem_enumerateLayer L h _).mp (maskAt_mem hi)




theorem subsetMask_setAt {L h i : ℕ} (hi : i < vertexCount L h) :
    subsetMask (setAt L h i) = maskAt L h i := subsetMask_decode (maskAt_spec hi).1
























































end ThreeSum.LocalMaskGraph

end

section


/-!
# Literal global-output records behind the radix key array

Local records use the verified layer enumerator's order and retain every
schedule occurrence. Cartesian extension enumerates each original global
output once. Mapping to integers may introduce equal values; the key array
retains all of those separate incidences.
-/

namespace ThreeSum.GlobalKeyEnumeration

open GlobalEncoding LocalGraph LocalCoverBounds LocalHashMoments
open RadixKeyLists
open scoped BigOperators

set_option maxHeartbeats 1800000

























































































































theorem localKeys_bounded (h : ℕ) :
    ∀ x ∈ localKeys h, |x| ≤ ((512*h*localPrime h : ℕ) : ℤ) := by
  intro x hx
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx
  exact rawOutput_abs_le _ _






end ThreeSum.GlobalKeyEnumeration

end

section


/-!
# Local output keys from ordinary stored masks and coefficient rows

This identifies the two nonnegative masked sums used by the imperative
local-key program with the unchanged signed `GlobalEncoding.rawOutput`.
-/

namespace ThreeSum.OutputKeyMasks

open GlobalEncoding LocalHashMoments LocalCoverBounds
open OneHotMask SubsetAddress
open scoped BigOperators

theorem extend_zero (L : ℕ) : extend (fun _ : Fin L => 0)=(fun _ : ℕ => 0) := by
  funext i
  simp [extend]

theorem eval_outside {L : ℕ} (Q : Finset (Fin L)) (w : Fin L → ℕ) :
    (eval (extend w) (fun _ => 0) L (subsetMask Q) : ℤ) =
      ∑ i : Fin L, if i ∈ Q then (0 : ℤ) else (w i : ℤ) := by
  rw [← extend_zero L,eval_subsetMask]
  push_cast
  rfl

theorem eval_difference {h L : ℕ} (w : Weight L (LocalField h))
    (Q : Finset (Fin L)) :
    (eval (extend fun i => (w (i,true)).val) (fun _ => 0) L (subsetMask Q) : ℤ)-
      (eval (extend fun i => (w (i,false)).val) (fun _ => 0) L (subsetMask Q) : ℤ)
      = rawOutput w Q := by
  rw [eval_outside,eval_outside,← Finset.sum_sub_distrib]
  unfold rawOutput
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ Q <;> simp [hi]

theorem mapRow_eq {h : ℕ} (b : Bool) (o : Occurrence h) :
    BlockCoefficientRows.mapRow h b o.val =
      extend (fun i : Fin (512*h) => (mapAt h o (i,b)).val) := by
  simp only [BlockCoefficientRows.mapRow,o.isLt,dite_true]

theorem indexed_blockKey {h : ℕ} (o : Occurrence h)
    (i : Fin ((512*h).choose (2*h))) :
    (eval (BlockCoefficientRows.mapRow h true o.val) (fun _ => 0) (512*h)
      (LocalMaskGraph.maskAt (512*h) (2*h) i.val) : ℤ)-
      (eval (BlockCoefficientRows.mapRow h false o.val) (fun _ => 0) (512*h)
      (LocalMaskGraph.maskAt (512*h) (2*h) i.val) : ℤ) =
      blockKey (o,GlobalKeyEnumeration.layerRecord h i) := by
  rw [mapRow_eq,mapRow_eq,← LocalMaskGraph.subsetMask_setAt i.isLt,eval_difference]
  rfl

end ThreeSum.OutputKeyMasks

end

section


/-!
# Exact local-output array semantics

The physical occurrence-major rows are the same list of original records
used by the verified global radix product constructor.
-/

namespace ThreeSum.LocalKeyArraySemantics

open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open Light

set_option maxHeartbeats 1800000
























theorem localKeys_eq_flatMap (h : ℕ) :
    localKeys h = (List.finRange (scheduleSize h)).flatMap
      (fun o => List.ofFn (fun i => blockKey (o,layerRecord h i))) := by
  simp only [localKeys,localRecords,List.product,List.map_flatMap,List.map_map,
    layers,List.map_ofFn,Function.comp_def]

theorem seg_localKeys {h dst : ℕ} {μ : ℕ → ℤ}
    (hout : ∀ j < scheduleSize h, ∀ i < outputCount (512*h) h,
      μ (dst+j*outputCount (512*h) h+i)=
        (OneHotMask.eval (BlockCoefficientRows.mapRow h true j) (fun _ => 0) (512*h)
          (LocalMaskGraph.maskAt (512*h) (2*h) i) : ℤ)-
        (OneHotMask.eval (BlockCoefficientRows.mapRow h false j) (fun _ => 0) (512*h)
          (LocalMaskGraph.maskAt (512*h) (2*h) i) : ℤ)) :
    Seg μ dst (localKeys h) := by
  rw [localKeys_eq_flatMap]
  apply seg_flatMap_rows _ _ (outputCount (512*h) h) dst (by simp [outputCount])
  intro j hj i hi
  have hj' : j < scheduleSize h := by simpa only [List.length_finRange] using hj
  rw [hout j hj' i hi]
  have he := OutputKeyMasks.indexed_blockKey ⟨j,hj'⟩ ⟨i,hi⟩
  have ho : (List.finRange (scheduleSize h))[j]=⟨j,hj'⟩ := by
    apply Fin.ext
    simp
  simpa only [List.getElem_ofFn,ho] using he

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets_original {pMain h masks maps dst free : ℕ} {μ : ℕ → ℤ}
    (S : LightLocalKeys.Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+3 ≤ lim.depth)
    (hspace : LightLocalKeyRow.space free (512*h) (outputCount (512*h) h) ≤ lim.space)
    (hmasks : masks+outputCount (512*h) h ≤ dst)
    (hmaps : maps+scheduleSize h*(2*(512*h)) ≤ dst)
    (hdst : dst+scheduleSize h*outputCount (512*h) h ≤ free)
    (hword : (LightLocalKeys.word (512*h) (localPrime h) (scheduleSize h) : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < outputCount (512*h) h,
      μ (masks+i)=(LocalMaskGraph.maskAt (512*h) (2*h) i : ℤ))
    (hreadFalse : ∀ j < scheduleSize h, ∀ i < 512*h,
      μ (maps+j*(2*(512*h))+i)=(BlockCoefficientRows.mapRow h false j i : ℤ))
    (hreadTrue : ∀ j < scheduleSize h, ∀ i < 512*h,
      μ (maps+j*(2*(512*h))+512*h+i)=(BlockCoefficientRows.mapRow h true j i : ℤ)) :
    Meets lim P pMain d [512*h,masks,outputCount (512*h) h,maps,scheduleSize h,dst,free] μ
      (LightLocalKeys.time (512*h) (outputCount (512*h) h) (scheduleSize h))
      (fun _ ν => Seg ν dst (localKeys h) ∧ Kept μ ν dst) := by
  apply (S.meets (U := localPrime h) (LocalMaskGraph.maskAt (512*h) (2*h))
    (BlockCoefficientRows.mapRow h false) (BlockCoefficientRows.mapRow h true)
    hw hd hspace hmasks hmaps hdst hword hmaskRead
    (fun i hi => (LocalMaskGraph.maskAt_spec hi).1) hreadFalse hreadTrue
    (fun j hj i hi => BlockCoefficientRows.mapRow_le false hj hi)
    (fun j hj i hi => BlockCoefficientRows.mapRow_le true hj hi)).mono le_rfl
  intro r ν ⟨hout,hkeep⟩
  exact ⟨seg_localKeys hout,hkeep⟩

end ThreeSum.LocalKeyArraySemantics

end

section


/-!
# From selected coefficient rows to every original global output key

The fixed program constructs the output-mask layer, all signed local keys,
and the full positional product. Its output is the literal occurrence-aware
`GlobalKeyEnumeration.globalKeys` array. No input key or mask table is assumed.
-/

namespace ThreeSum.LightGlobalKeys

open Light GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open LightSubsetAddress SubsetAddress

set_option maxHeartbeats 600000
set_option maxRecDepth 10000


























private theorem sum_parts (a b c j : ℕ) :
    a ≤ a+b+c+j+512 ∧ b ≤ a+b+c+j+512 ∧
    c ≤ a+b+c+j+512 ∧ j ≤ a+b+c+j+512 := by omega

private theorem word_parts (h J : ℕ) :
    2^(512*h+1) ≤ word h J ∧
    LightLocalKeys.word (512*h) (localPrime h) (scheduleSize h) ≤ word h J ∧
    LightRadixKeys.word (localPrime h) (512*h*localPrime h) J ≤ word h J ∧
    J ≤ word h J :=
  sum_parts _ _ _ _

private theorem int_mul_le_word {a b c : ℕ} {w : ℤ}
    (hab : a*b ≤ c) (hc : (c : ℤ) ≤ w) : (a : ℤ)*(b : ℤ) ≤ w := by
  exact (show (a : ℤ)*(b : ℤ) ≤ (c : ℤ) by
    simpa only [Nat.cast_mul] using Int.ofNat_le.mpr hab).trans hc

theorem localCount_pos (h : ℕ) : 0 < localCount h := by
  apply Nat.mul_pos
  · unfold scheduleSize scheduleLength
    positivity
  · exact Nat.choose_pos (by omega)

theorem localKeys_length (h : ℕ) : (localKeys h).length=localCount h := by
  simp [localKeys,localRecords_length,localCount]


















variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets_with_masks_sourceProof {pMain h J maps free : ℕ} {μ : ℕ → ℤ} (S : Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+J+5 ≤ lim.depth)
    (hspace : space free h J ≤ lim.space) (hword : (word h J : ℤ) ≤ lim.word)
    (hmaps : maps+scheduleSize h*(2*(512*h)) ≤ free)
    (hreadFalse : ∀ j < scheduleSize h, ∀ i < 512*h,
      μ (maps+j*(2*(512*h))+i)=(BlockCoefficientRows.mapRow h false j i : ℤ))
    (hreadTrue : ∀ j < scheduleSize h, ∀ i < 512*h,
      μ (maps+j*(2*(512*h))+512*h+i)=(BlockCoefficientRows.mapRow h true j i : ℤ)) :
    Meets lim P pMain d [512*h,2*h,scheduleSize h,localPrime h,J,maps,
      outputCount (512*h) h,free] μ (time h J)
      (fun r ν => r=((scratch free h+LightRadixKeys.offset (localCount h) J : ℕ) : ℤ) ∧
        ν (scratch free h+LightRadixKeys.offset (localCount h) J)=((localCount h^J : ℕ) : ℤ) ∧
        Seg ν (scratch free h+LightRadixKeys.offset (localCount h) J+1) (globalKeys h J) ∧
        (∀ i < outputCount (512*h) h,
          ν (free+i)=(LocalMaskGraph.maskAt (512*h) (2*h) i : ℤ)) ∧
        Kept μ ν free) := by
  let n := outputCount (512*h) h
  let m := localCount h
  let dst := free+n
  let work := scratch free h
  have hwork : work=dst+m := rfl
  have hlspace : LightLocalKeyRow.space work (512*h) n ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hgspace : LightRadixKeys.space work m J ≤ lim.space :=
    (le_max_right _ _).trans hspace
  have hs : work+512*h+2*n+(512*h+1) ≤ lim.space := hlspace
  have hbudget (x : ℕ) (hx : x ≤ word h J) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hpword := hbudget (2^(512*h+1)) (word_parts h J).1
  have hlword := hbudget (LightLocalKeys.word (512*h) (localPrime h) (scheduleSize h)) (word_parts h J).2.1
  have hgword := hbudget (LightRadixKeys.word (localPrime h) (512*h*localPrime h) J) (word_parts h J).2.2.1
  have hJword := hbudget J (word_parts h J).2.2.2
  have hcount := localCount_pos h
  have hlen : (localKeys h).length=m := localKeys_length h
  have hprodWord : (scheduleSize h : ℤ)*(n : ℤ) ≤ lim.word := by
    have hh : scheduleSize h*n ≤ lim.space := by change m ≤ lim.space; omega
    exact int_mul_le_word hh hw
  have hprodNonneg : (0 : ℤ) ≤ (scheduleSize h : ℤ)*(n : ℤ) :=
    mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hprodWord' : (scheduleSize h : ℤ)*(outputCount (512*h) h : ℤ) ≤ lim.word := hprodWord
  have hprodNonneg' : (0 : ℤ) ≤ (scheduleSize h : ℤ)*(outputCount (512*h) h : ℤ) :=
    mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hproduct : (scheduleSize h : ℤ)*(outputCount (512*h) h : ℤ)=(m : ℤ) := by
    simp only [m,localCount,Nat.cast_mul]
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
    (refine
        Light.Ends.setToThen (scheduleSize h * outputCount (512 * h) h : ℕ) ?_ ?_
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
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
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
    (refine Light.Ends.setToThen (dst : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, dst,
                n]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [dst, n] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, dst, n] <;> omega)));
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
    (refine Light.Ends.setToThen (work : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hwork,
                hproduct]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hwork, hproduct] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hwork, hproduct] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  have he := LightSubsetEnumerationSetup.meets (d := d+1) (μ := μ)
    (L := 512*h) (k := 2*h) (dst := free) (work := work)
    S.enum S.powers S.layer hw (by omega) hpword (by omega)
    (by change free+n ≤ work; dsimp [dst] at hwork; omega) (by omega)
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
      | refine Light.Ends.callToThen (he _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen he ?_ ?_ ?_ ?_);
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
        ((rintro count μ₁ ⟨hcountVal, hmasks, hpowers, hkeep₁⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hc : count=(n : ℤ) := hcountVal
  have hmRead (i : ℕ) (hi : i < n) : μ₁ (free+i)=(LocalMaskGraph.maskAt (512*h) (2*h) i : ℤ) := by
    have hi' : i < (enumerateLayer (512*h) (2*h)).length := by
      rw [enumerateLayer_length]
      exact hi
    have he := hmasks i (by simpa only [List.length_map] using hi')
    simpa only [LocalMaskGraph.maskAt,List.getD_eq_getElem _ _ hi',List.getElem_map] using he
  have hfi (j : ℕ) (hj : j < scheduleSize h) (i : ℕ) (hi : i < 512*h) :
      μ₁ (maps+j*(2*(512*h))+i)=(BlockCoefficientRows.mapRow h false j i : ℤ) := by
    have hh := Nat.mul_le_mul_right (2*(512*h)) (show j+1 ≤ scheduleSize h by omega)
    simp only [Nat.add_mul,one_mul] at hh
    rw [hkeep₁ _ ⟨by omega,Or.inl (by omega)⟩]
    exact hreadFalse j hj i hi
  have hti (j : ℕ) (hj : j < scheduleSize h) (i : ℕ) (hi : i < 512*h) :
      μ₁ (maps+j*(2*(512*h))+512*h+i)=(BlockCoefficientRows.mapRow h true j i : ℤ) := by
    have hh := Nat.mul_le_mul_right (2*(512*h)) (show j+1 ≤ scheduleSize h by omega)
    simp only [Nat.add_mul,one_mul] at hh
    rw [hkeep₁ _ ⟨by omega,Or.inl (by omega)⟩]
    exact hreadTrue j hj i hi
  have hl := LocalKeyArraySemantics.meets_original (d := d+1) (μ := μ₁)
    (h := h) (masks := free) (maps := maps) (dst := dst) (free := work) S.locals
    hw (by omega) hlspace le_rfl (by dsimp [dst]; omega) (by dsimp [localCount,m] at *; omega)
    hlword hmRead hfi hti
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
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hc]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hc] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hc] <;> omega)));
    (on_goal -1 =>
        ((rintro result μ₂ ⟨hkeys, hkeep₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hg := LightRadixKeys.meets (src := dst) (dst := work) (p := localPrime h)
    (U := 512*h*localPrime h) S.globalProc S.rows S.affine (localKeys h) hw
    (by rw [hlen]; omega) (by rw [hlen]; exact hcount) (localKeys_bounded h)
    J (d+1) μ₂ (by simpa only [hlen] using hgspace) hgword (by omega) hkeys
  simp only [hlen] at hg
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
      | refine Light.Ends.callToThen (hg _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hg ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, m]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [m] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, m] <;> omega)));
    (on_goal -1 =>
        ((rintro final μ₃ ⟨hresult, hheader, hglobal, hkeep₃⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  refine ⟨hresult,hheader,hglobal,?_,?_⟩
  · intro i hi
    change μ₃ (free+i)=(LocalMaskGraph.maskAt (512*h) (2*h) i : ℤ)
    rw [hkeep₃ _ (by dsimp [dst] at hwork; change i < n at hi; omega),
      hkeep₂ _ (by dsimp [dst]; change i < n at hi; omega)]
    exact hmRead i hi
  · intro a ha
    change μ₃ a=μ a
    rw [hkeep₃ _ (by omega),hkeep₂ _ (by dsimp [dst]; omega),
      hkeep₁ _ ⟨by omega,Or.inl ha⟩]












































end ThreeSum.LightGlobalKeys

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain h J maps free : Nat} {μ : Nat → Int}
  (S : ThreeSum.LightGlobalKeys.Procs P pMain),
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
            J)
          (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
        lim.depth →
      @LE.le.{0} Nat instLENat (ThreeSum.LightGlobalKeys.space free h J) lim.space →
        @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightGlobalKeys.word h J)) lim.word →
          @LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (ThreeSum.GlobalEncoding.scheduleSize h)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
              free →
            (∀ (j : Nat),
                @LT.lt.{0} Nat instLTNat j (ThreeSum.GlobalEncoding.scheduleSize h) →
                  ∀ (i : Nat),
                    @LT.lt.{0} Nat instLTNat i
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h) →
                      @Eq.{1} Int
                        (μ
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) j
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
                            i))
                        (@Nat.cast.{0} Int instNatCastInt (ThreeSum.BlockCoefficientRows.mapRow h Bool.false j i))) →
              (∀ (j : Nat),
                  @LT.lt.{0} Nat instLTNat j (ThreeSum.GlobalEncoding.scheduleSize h) →
                    ∀ (i : Nat),
                      @LT.lt.{0} Nat instLTNat i
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h) →
                        @Eq.{1} Int
                          (μ
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) j
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                              i))
                          (@Nat.cast.{0} Int instNatCastInt (ThreeSum.BlockCoefficientRows.mapRow h Bool.true j i))) →
                Light.Meets lim P pMain d
                  (@List.cons.{0} Int
                    (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                      (@OfNat.ofNat.{0} Int (nat_lit 512) (@instOfNat (nat_lit 512)))
                      (@Nat.cast.{0} Int instNatCastInt h))
                    (@List.cons.{0} Int
                      (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                        (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))
                        (@Nat.cast.{0} Int instNatCastInt h))
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.GlobalEncoding.scheduleSize h))
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LocalCoverBounds.localPrime h))
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt J)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt maps)
                              (@List.cons.{0} Int
                                (@Nat.cast.{0} Int instNatCastInt
                                  (ThreeSum.LocalCoverBounds.outputCount
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                    h))
                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt free) (@List.nil.{0} Int)))))))))
                  μ (ThreeSum.LightGlobalKeys.time h J) fun (r : Int) (ν : Nat → Int) =>
                  And
                    (@Eq.{1} Int r
                      (@Nat.cast.{0} Int instNatCastInt
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (ThreeSum.LightGlobalKeys.scratch free h)
                          (ThreeSum.LightRadixKeys.offset (ThreeSum.LightGlobalKeys.localCount h) J))))
                    (And
                      (@Eq.{1} Int
                        (ν
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (ThreeSum.LightGlobalKeys.scratch free h)
                            (ThreeSum.LightRadixKeys.offset (ThreeSum.LightGlobalKeys.localCount h) J)))
                        (@Nat.cast.{0} Int instNatCastInt
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                            (ThreeSum.LightGlobalKeys.localCount h) J)))
                      (And
                        (Light.Seg ν
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (ThreeSum.LightGlobalKeys.scratch free h)
                              (ThreeSum.LightRadixKeys.offset (ThreeSum.LightGlobalKeys.localCount h) J))
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (ThreeSum.GlobalKeyEnumeration.globalKeys h J))
                        (And
                          (∀ (i : Nat),
                            @LT.lt.{0} Nat instLTNat i
                                (ThreeSum.LocalCoverBounds.outputCount
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                  h) →
                              @Eq.{1} Int (ν (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) free i))
                                (@Nat.cast.{0} Int instNatCastInt
                                  (ThreeSum.LocalMaskGraph.maskAt
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)
                                    i)))
                          (Light.Kept μ ν free)))) := by
  exact @ThreeSum.LightGlobalKeys.Procs.meets_with_masks_sourceProof

#print axioms solution
