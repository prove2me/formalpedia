-- Prove2me | solution 1 for ThreeSum.LightGuardedWanted.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:59:34.993251+00:00
-- url     : https://prove2.me/submissions/685c9628-f711-488a-804a-931fc3865d4a

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
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
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
import Theorems.Thm_ThreeSum_GlobalKeyEnumeration_rawOutput_abs_le
import Theorems.Thm_ThreeSum_LightBalancedWanted_program_meets
import Theorems.Thm_ThreeSum_LightCoverKeyData_Stored_of_kept
import Theorems.Thm_ThreeSum_LightCoverKeys_Procs_meets_with_masks
import Theorems.Thm_ThreeSum_LightRawAKeys_meets
import Theorems.Thm_ThreeSum_RadixKeyLists_values_bounded


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
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSum.RawAKeyLists
end ThreeSum.RawAKeyLists
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
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


































































































theorem globalKeys_length (h J : ℕ) :
    (globalKeys h J).length=scheduleSize h^J*outputCount (512*h) h^J := by
  rw [globalKeys_eq_map,List.length_map,globalRecords_length]




















theorem localKeys_bounded (h : ℕ) :
    ∀ x ∈ localKeys h, |x| ≤ ((512*h*localPrime h : ℕ) : ℤ) := by
  intro x hx
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx
  exact rawOutput_abs_le _ _

theorem globalKeys_bounded (h J : ℕ) :
    ∀ x ∈ globalKeys h J,
      |x| ≤ (((512*h*localPrime h)*(localPrime h+1)^J : ℕ) : ℤ) :=
  values_bounded _ _ _ (localKeys_bounded h) J

end ThreeSum.GlobalKeyEnumeration

end

section


/-!
# Original-index incidences in the guarded global encoding

An incidence retains its original input indices, its complete sequence of
chosen-map occurrences and retained local edges, and its signed arithmetic
lift. Equal input values remain distinct original indices. The lift is
unique for a fixed original triple and representation, so it does not add
a factor of three to the representation bound.
-/

namespace ThreeSum.RawIncidences

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds



theorem lift_small (j : Fin 3) : Arithmetic.SmallLift (lift j) := by
  fin_cases j <;> simp [lift, Arithmetic.SmallLift]



























































































































































































































section OriginalIndices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]



























































































































































































































end OriginalIndices

end ThreeSum.RawIncidences

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




















































end ThreeSum.LightLocalCoverRetention

end

section


/-!
# The retained cover, output layers, and exact global key array

This bundle is produced by the actual cover/key host and remains valid when
later phases use its computed next free address. In particular the output
index decoder can read the original layer masks without reconstructing them.
-/

namespace ThreeSum.LightCoverKeyData

open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000




theorem global_length (h J : ℕ) : (globalKeys h J).length=LightGlobalKeys.localCount h^J := by
  simp only [globalKeys_length,LightGlobalKeys.localCount,mul_pow]

theorem layer_end_le_header (free h J : ℕ) :
    LightCoverKeys.afterCover free h+outputCount (512*h) h ≤ LightCoverKeys.keyHeader free h J := by
  unfold LightCoverKeys.keyHeader LightGlobalKeys.scratch
  omega

theorem afterCover_le_keyEnd (free h J : ℕ) : LightCoverKeys.afterCover free h ≤ keyEnd free h J := by
  have hh := layer_end_le_header free h J
  unfold keyEnd
  omega

theorem free_le_keyEnd (free h J : ℕ) : free ≤ keyEnd free h J := by
  have hh := LightLocalCoverRetention.base_le_nextFree (LightLocalCoverInit.base free) h
  have hk := afterCover_le_keyEnd free h J
  change free+20 ≤ LightCoverKeys.afterCover free h at hh
  omega







































theorem program_meets {lim : Limits} {μ : ℕ → ℤ} {h J free d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+J+11 ≤ lim.depth)
    (hspace : LightCoverKeys.space free h J ≤ lim.space)
    (hword : (LightCoverKeys.word h J : ℤ) ≤ lim.word) :
    Meets lim LightCoverKeys.program 67 d [h,J,free] μ (LightCoverKeys.time h J)
      (fun r ν => r=(LightCoverKeys.keyHeader free h J : ℤ) ∧ Stored ν free h J ∧ Kept μ ν free) := by
  exact (LightCoverKeys.programProcs.meets_with_masks hw hd hspace hword).mono le_rfl
    (fun _ _ ⟨hr,hc,hk,hh,hd,hs,hi,hm,hkeep⟩ => ⟨hr,⟨hc,hk,hh,hd,hs,hi,hm⟩,hkeep⟩)

end ThreeSum.LightCoverKeyData

end

section


/-!
# Original A positions and all three guarded lifts

The physical key order is lift-major, preserving every original position.
The selected-offset count is transported to the unchanged guarded wanted
labels used by raw reporting, including repeated input values.
-/

namespace ThreeSum.RawAKeyLists

open GlobalEncoding RawIncidences GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open scoped BigOperators

set_option maxHeartbeats 900000






















theorem keys_length (P : ℤ) (xs : List ℤ) : (keys P xs).length=3*xs.length := by
  rw [keys,List.length_map,records_length]





























theorem key_bounded {P : ℤ} (hP : 0 < P) (xs : List ℤ) (r : Record xs) :
    |key P xs r| ≤ 2*P := by
  have hn := Int.emod_nonneg (xs.getD r.2.val 0) hP.ne'
  have hu := Int.emod_lt_of_pos (xs.getD r.2.val 0) hP
  have hl : -1 ≤ lift r.1 ∧ lift r.1 ≤ 1 := by
    rcases lift_small r.1 with hh | hh | hh <;> rw [hh] <;> norm_num
  unfold key
  apply abs_le.mpr
  constructor <;> nlinarith

theorem keys_bounded {P : ℤ} (hP : 0 < P) (xs : List ℤ) :
    ∀ x ∈ keys P xs, |x| ≤ 2*P := by
  intro x hx
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp hx
  exact key_bounded hP xs r































































end ThreeSum.RawAKeyLists

end

section


/-!
# Actual construction of the three lifted original A-key arrays

The middle row is computed by the checked signed remainder routine. Two
affine scans append the minus and plus lifts. Every original position is
retained in each row, and the resulting segment is the exact guarded-key
list whose balancing bound is proved in `RawAKeyLists`.
-/

namespace ThreeSum.LightRawAKeys

open Light LightResidues RawIncidences RawAKeyLists

set_option maxHeartbeats 1000000
set_option maxRecDepth 6000













variable {lim : Limits} {P : Program} {d : ℕ}


















































































theorem program_meets {src free p U : ℕ} {μ : ℕ → ℤ} (xs : List ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 0 < p)
    (hsrc : src+xs.length ≤ free)
    (hspace : space free xs.length U ≤ lim.space)
    (hword : (word p U : ℤ) ≤ lim.word) (hd : d+2 ≤ lim.depth)
    (hread : Seg μ src xs) (hvalues : ∀ x ∈ xs, |x| ≤ (U : ℤ)) :
    Meets lim program 0 d [src,xs.length,p,free] μ (time xs.length U)
      (fun r ν => r=(free : ℤ) ∧ Seg ν free (keys p xs) ∧ Kept μ ν free) :=
  meets rfl rfl rfl rfl xs hw hp hsrc hspace hword hd hread hvalues





end ThreeSum.LightRawAKeys

end

section


/-!
# Exact relocation of closed verified procedure libraries

Every procedure call is shifted by the same list offset. The structural
execution proof preserves the exact initial/final states, runtime, memory
addresses, values, and depth budget. It permits composition of independently
verified fixed programs without assuming a new implementation contract.
-/

namespace ThreeSum.ReportingHostRelocation

open Light












theorem lookup {P : Program} {p : ℕ} {body : Stmt} (h : P[p]? = some body) (prefixProgram : Program) :
    (program prefixProgram P)[prefixProgram.length+p]? = some (relocate prefixProgram.length body) := by
  apply getElem?_append_length_add
  rw [List.getElem?_map,h]
  rfl

theorem exec {lim : Limits} {P : Program} {d : ℕ} {s : Stmt} {σ σ' : State} {c : ℕ}
    (h : Exec lim P d s σ σ' c) (prefixProgram : Program) :
    Exec lim (program prefixProgram P) d (relocate prefixProgram.length s) σ σ' c := by
  induction h with
  | skip => exact .skip
  | set h => exact .set h
  | store h₁ h₂ h₃ => exact .store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact .iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact .iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact .whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact .whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact .call h₁ (lookup h₂ prefixProgram) h₃ ih

theorem ends {lim : Limits} {P : Program} {d : ℕ} {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop}
    (h : Ends lim P d s σ T Q) (prefixProgram : Program) :
    Ends lim (program prefixProgram P) d (relocate prefixProgram.length s) σ T Q := by
  obtain ⟨σ',c,he,hc,hq⟩ := h
  exact ⟨σ',c,exec he prefixProgram,hc,hq⟩

theorem meets {lim : Limits} {P : Program} {p d : ℕ} {vals : List ℤ} {μ : ℕ → ℤ}
    {T : ℕ} {R : ℤ → (ℕ → ℤ) → Prop} (h : Meets lim P p d vals μ T R) (prefixProgram : Program) :
    Meets lim (program prefixProgram P) (prefixProgram.length+p) d vals μ T R := by
  obtain ⟨body,hbody,he⟩ := h
  exact ⟨relocate prefixProgram.length body,lookup hbody prefixProgram,ends he prefixProgram⟩

end ThreeSum.ReportingHostRelocation

end

section


/-!
# Actual cover construction, lifted A keys, and balanced wanted records

This closed program runs the local-cover initializer and global key product,
constructs all three lifts of the supplied A incidences, selects the common
offset, and emits precisely the matching position pairs. Every dimension and
output address is read or computed. The retained cover, layers and coefficient
tables are available to the source-bank and output-decoding phases afterwards.
-/

namespace ThreeSum.LightGuardedWanted

open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds

set_option maxHeartbeats 2400000
set_option maxRecDepth 10000








































theorem selected_eq (P M h J : ℕ) [NeZero M] (xs : List ℤ) :
    LightOriginalOffset.selected M (left P xs) (right h J) (3*xs.length) (totalKeys h J)=
      RawAKeyLists.selected M P xs h J := by
  unfold RawAKeyLists.selected GlobalKeyOffset.selected
  rw [RawAKeyLists.keys_length,LightCoverKeyData.global_length]
  rfl

theorem left_bound {P h J : ℕ} (hP : 0 < P) (xs : List ℤ) (i : ℕ) (hi : i < 3*xs.length) :
    |left P xs i| ≤ (keyBound P h J : ℤ) := by
  have hi' : i < (RawAKeyLists.keys P xs).length := by rwa [RawAKeyLists.keys_length]
  unfold left
  rw [List.getD_eq_getElem _ _ hi']
  have hh := RawAKeyLists.keys_bounded (by exact_mod_cast hP : (0 : ℤ) < P)
    xs _ (List.getElem_mem hi')
  have hb : 2*P ≤ keyBound P h J := by unfold keyBound; omega
  exact hh.trans (by exact_mod_cast hb)

theorem right_bound (h J P : ℕ) (j : ℕ) (hj : j < totalKeys h J) :
    |right h J j| ≤ (keyBound P h J : ℤ) := by
  have hj' : j < (globalKeys h J).length := by rwa [LightCoverKeyData.global_length]
  unfold right
  rw [List.getD_eq_getElem _ _ hj']
  have hh := globalKeys_bounded h J _ (List.getElem_mem hj')
  have hb : (512*h*localPrime h)*(localPrime h+1)^J ≤ keyBound P h J := by
    unfold keyBound
    omega
  exact hh.trans (Int.ofNat_le.mpr hb)

variable {lim : Limits}

theorem program_meets_sourceProof {μ : ℕ → ℤ} {a free P M h J U d : ℕ} [NeZero M] (xs : List ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hP : 0 < P) (ha : a+xs.length ≤ free)
    (hspace : space free P M h J U xs ≤ lim.space)
    (hword : (word P M h J U xs.length : ℤ) ≤ lim.word)
    (hd : d+512*h+J+Nat.clog 2 M+3*xs.length+12 ≤ lim.depth)
    (hread : Seg μ a xs) (hvalues : ∀ x ∈ xs, |x| ≤ (U : ℤ)) :
    Meets lim program 98 d [h,J,a,xs.length,P,M,free] μ (time P M h J U xs)
      (fun r ν => r=(wantedFree free h J xs.length : ℤ) ∧
        LightWantedSetup.Output ν (wantedFree free h J xs.length) M (left P xs) (right h J)
          (3*xs.length) (totalKeys h J) (RawAKeyLists.selected M P xs h J) ∧
        M*(ν (wantedFree free h J xs.length)).toNat ≤ 3*xs.length*totalKeys h J ∧
        LightCoverKeyData.Stored ν free h J ∧
        Seg ν (LightCoverKeyData.keyEnd free h J) (RawAKeyLists.keys P xs) ∧ Kept μ ν free) := by
  let keyHead := LightCoverKeys.keyHeader free h J
  let rawBase := LightCoverKeyData.keyEnd free h J
  let out := wantedFree free h J xs.length
  have hkeyEnd : rawBase=keyHead+1+totalKeys h J := rfl
  have hout : out=rawBase+3*xs.length := rfl
  have hcoverSpace : LightCoverKeys.space free h J ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hliftSpace : LightRawAKeys.space rawBase xs.length U ≤ lim.space :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hspace)
  have hwantedSpace : LightBalancedWanted.space out M (left P xs) (right h J)
      (3*xs.length) (totalKeys h J) (keyBound P h J) ≤ lim.space :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hspace)
  have hcoverWord : (LightCoverKeys.word h J : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_left _ _)).trans hword
  have hliftWord : (LightRawAKeys.word P U : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ((le_max_left _ _).trans (le_max_right _ _))).trans hword
  have hwantedWord : (LightBalancedWanted.word M (3*xs.length) (totalKeys h J) (keyBound P h J) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ((le_max_right _ _).trans (le_max_right _ _))).trans hword
  have hrawSpace : rawBase+3*xs.length+Nat.log 2 (U+1)+2 ≤ lim.space := hliftSpace
  have hfree : free ≤ rawBase := LightCoverKeyData.free_le_keyEnd free h J
  have htripleWord : (3*(xs.length : ℤ)) ≤ lim.word :=
    (by exact_mod_cast (show 3*xs.length ≤ lim.space by omega) :
      (3*(xs.length : ℤ)) ≤ lim.space).trans hw
  apply Meets.of_body (p := 98) (by rfl : program[98]? = some (body 67 68 97))
  unfold body time
  have hc := (((LightCoverKeyData.program_meets (d := d+1) (μ := μ) (h := h) (J := J)
    (free := free) hw (by omega) hcoverSpace hcoverWord).append
      (LightRawAKeys.program.map (ReportingHostRelocation.relocate 68))).append
      (LightBalancedWanted.program.map (ReportingHostRelocation.relocate 72))).append [body 67 68 97]
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
        ((rintro header μ₁ ⟨hheader, H, hkeepC⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hcount := H.count
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (totalKeys h J : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hheader,
                hcount, totalKeys]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hheader, hcount, totalKeys] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hheader, hcount,
                totalKeys] <;>
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
    (refine Light.Ends.setToThen (keyHead + 1 : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hheader,
                keyHead]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hheader, keyHead] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hheader, keyHead] <;>
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
    (refine Light.Ends.setToThen (rawBase : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hkeyEnd]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hkeyEnd] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hkeyEnd] <;> omega)));
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
    (refine Light.Ends.setToThen (3 * xs.length : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (out : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hout]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hout] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hout] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  have hx₁ : Seg μ₁ a xs := by
    apply hread.congr
    intro i hi
    exact hkeepC _ (by omega)
  have hl := ((ReportingHostRelocation.meets
    (LightRawAKeys.program_meets (d := d+1) (μ := μ₁) (src := a) (free := rawBase)
      (p := P) (U := U) xs hw hP (by omega) hliftSpace hliftWord (by omega) hx₁ hvalues)
    LightCoverKeys.program).append
      (LightBalancedWanted.program.map (ReportingHostRelocation.relocate 72))).append [body 67 68 97]
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
        ((rintro rawHead μ₂ ⟨hrawHead, hraw, hkeepL⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hleft (i : ℕ) (hi : i < 3*xs.length) : μ₂ (rawBase+i)=left P xs i := by
    have hi' : i < (RawAKeyLists.keys P xs).length := by rwa [RawAKeyLists.keys_length]
    rw [left,List.getD_eq_getElem _ _ hi']
    exact hraw i hi'
  have hright (j : ℕ) (hj : j < totalKeys h J) : μ₂ (keyHead+1+j)=right h J j := by
    have hj' : j < (globalKeys h J).length := by rwa [LightCoverKeyData.global_length]
    rw [hkeepL _ (by omega),right,List.getD_eq_getElem _ _ hj']
    exact H.keys j hj'
  have hb := (ReportingHostRelocation.meets
    (LightBalancedWanted.program_meets (d := d+1) (μ := μ₂) (a := rawBase) (b := keyHead+1)
      (NL := 3*xs.length) (NR := totalKeys h J) (M := M) (free := out) (U := keyBound P h J)
      (left P xs) (right h J) hw (by omega) (by omega) hwantedSpace hwantedWord (by omega)
      hleft hright (left_bound hP xs) (right_bound h J P)) liftProgram).append [body 67 68 97]
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
      | refine Light.Ends.callToThen (hb _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hb ?_ ?_ ?_ ?_);
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
        ((rintro result ν ⟨hresult, houtput, hbound, hkeepB⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hretain : Kept μ₁ ν rawBase := by
    intro i hi
    exact (hkeepB _ (by omega)).trans (hkeepL i hi)
  refine ⟨hresult,?_,hbound,H.of_kept hretain,?_,?_⟩
  · simpa only [selected_eq] using houtput
  · apply hraw.congr
    intro i hi
    rw [RawAKeyLists.keys_length] at hi
    exact hkeepB _ (by omega)
  · intro i hi
    exact (hretain i (by omega)).trans (hkeepC i hi)

end ThreeSum.LightGuardedWanted

end


theorem solution : ∀ {lim : Light.Limits} {μ : Nat → Int} {a free P M h J U d : Nat}
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (xs : List.{0} Int),
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P →
      @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a (@List.length.{0} Int xs)) free →
        @LE.le.{0} Nat instLENat (@ThreeSum.LightGuardedWanted.space free P M h J U inst xs) lim.space →
          @LE.le.{0} Int Int.instLEInt
              (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightGuardedWanted.word P M h J U (@List.length.{0} Int xs)))
              lim.word →
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                        J)
                      (Nat.clog (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) M))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@List.length.{0} Int xs)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
                lim.depth →
              Light.Seg μ a xs →
                (∀ (x : Int),
                    @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) xs x →
                      @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup x)
                        (@Nat.cast.{0} Int instNatCastInt U)) →
                  Light.Meets lim ThreeSum.LightGuardedWanted.program
                    (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98))) d
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt h)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt J)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int xs))
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt P)
                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt M)
                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt free) (@List.nil.{0} Int))))))))
                    μ (@ThreeSum.LightGuardedWanted.time P M h J U inst xs) fun (r : Int) (ν : Nat → Int) =>
                    And
                      (@Eq.{1} Int r
                        (@Nat.cast.{0} Int instNatCastInt
                          (ThreeSum.LightGuardedWanted.wantedFree free h J (@List.length.{0} Int xs))))
                      (And
                        (ThreeSum.LightWantedSetup.Output ν
                          (ThreeSum.LightGuardedWanted.wantedFree free h J (@List.length.{0} Int xs)) M
                          (ThreeSum.LightGuardedWanted.left P xs) (ThreeSum.LightGuardedWanted.right h J)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@List.length.{0} Int xs))
                          (ThreeSum.LightGuardedWanted.totalKeys h J)
                          (@Nat.cast.{0} Int instNatCastInt
                            (@ThreeSum.RawAKeyLists.selected M inst (@Nat.cast.{0} Int instNatCastInt P) xs h J)))
                        (And
                          (@LE.le.{0} Nat instLENat
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) M
                              (ν (ThreeSum.LightGuardedWanted.wantedFree free h J (@List.length.{0} Int xs))).toNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@List.length.{0} Int xs))
                              (ThreeSum.LightGuardedWanted.totalKeys h J)))
                          (And (ThreeSum.LightCoverKeyData.Stored ν free h J)
                            (And
                              (Light.Seg ν (ThreeSum.LightCoverKeyData.keyEnd free h J)
                                (ThreeSum.RawAKeyLists.keys (@Nat.cast.{0} Int instNatCastInt P) xs))
                              (Light.Kept μ ν free))))) := by
  exact @ThreeSum.LightGuardedWanted.program_meets_sourceProof

#print axioms solution
