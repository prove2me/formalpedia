-- Prove2me | solution 1 for ThreeSum.LightReportingInitialize.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T17:15:03.669854+00:00
-- url     : https://prove2.me/submissions/7bec4e7b-75fc-43e8-b402-1e831d82f31a

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
import Mathlib.Data.Finset.Range
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
import Mathlib.Data.List.ProdSigma
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
import Theorems.Thm_ThreeSum_LightReportingCatalogQuery_program_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.ReportingHostPrefixOrder
end ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSumApsp
end ThreeSumApsp

section


/-! # Exact arithmetic subtraction of one subset mask from another -/

namespace ThreeSum.MaskDifference

open Finset ThreeSum.SubsetAddress

theorem subsetMask_sum {L : ℕ} (S : Finset (Fin L)) :
    subsetMask S = ∑ i ∈ S, 2^i.val := by
  simp [subsetMask,maskOf,natPositions]

@[simp] theorem subsetMask_empty (L : ℕ) : subsetMask (∅ : Finset (Fin L)) = 0 := by
  simp [subsetMask_sum]











































end ThreeSum.MaskDifference

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

theorem Ends.store {σ T a e} {Q : State → Prop} (ha : a.Safe lim σ) (he : e.Safe lim σ)
    (hA : lim.Addr (a.val σ)) (hT : a.cost + e.cost + 1 ≤ T)
    (h : Q { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) }) :
    Ends lim P d (.store a e) σ T Q :=
  ⟨_, _, .store ha he hA, hT, h⟩

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




















































/-- A branch, followed by the rest of the program: each side, with the rest of the program behind
it, gets the steps that the test leaves. -/
theorem Ends.iteThen {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ s : Stmt} {Q : State → Prop}
    (h₁ : c.Holds σ → Ends lim P d ((Light.Stmt.seq s₁ s)) σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → Ends lim P d ((Light.Stmt.seq s₂ s)) σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ := by (((try have := Light.Std.space_le (by assumption)));
                                ((try have := Light.Std.const_le (by assumption)));
                                (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) (hT : c.cost + 1 ≤ T := by first
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
    Ends lim P d ((Light.Stmt.seq (.ite c s₁ s₂) s)) σ T Q := by
  by_cases hc : c.Holds σ
  · obtain ⟨σ'', _, he, hk, hq⟩ := h₁ hc
    cases he with
    | seq he₁ he₂ => exact ⟨σ'', _, .seq (.iteTrue hs hc he₁) he₂, by omega, hq⟩
  · obtain ⟨σ'', _, he, hk, hq⟩ := h₂ hc
    cases he with
    | seq he₁ he₂ => exact ⟨σ'', _, .seq (.iteFalse hs hc he₁) he₂, by omega, hq⟩

/-- A branch, followed by the rest of the program, where the test says `p`: the first side is run
under the hypothesis `p`, the second under `¬ p`. -/
theorem Ends.iteIffThen {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ s : Stmt} {Q : State → Prop}
    (p : Prop) (h₁ : p → Ends lim P d ((Light.Stmt.seq s₁ s)) σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ p → Ends lim P d ((Light.Stmt.seq s₂ s)) σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ ∧ (c.Holds σ ↔ p) := by (((try have := Light.Std.space_le (by assumption)));
                                                       ((try have := Light.Std.const_le (by assumption)));
                                                       (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : c.cost + 1 ≤ T := by first
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
                                       | ((ring_nf); (omega)))) : Ends lim P d ((Light.Stmt.seq (.ite c s₁ s₂) s)) σ T Q :=
  Ends.iteThen (fun hc => h₁ (hs.2.1 hc)) (fun hc => h₂ fun hp => hc (hs.2.2 hp)) hs.1 hT

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

/-- `mem[a] := e`, where a gives the address b, which lies in the memory, and e gives z. -/
theorem Ends.storeTo {a e : Expr} (b : ℕ) (z : ℤ) (h : Q ⟨frame l, Function.update μ b z⟩)
    (he : a.Gives lim ⟨frame l, μ⟩ b ∧ e.Gives lim ⟨frame l, μ⟩ z ∧ b < lim.space := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : a.cost + e.cost + 1 ≤ T := by first
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
    Ends lim P d (.store a e) ⟨frame l, μ⟩ T Q := by
  obtain ⟨⟨ha, hav⟩, ⟨he, hev⟩, hb⟩ := he
  refine Ends.store ha he ?_ hT ?_
  · rw [hav]
    exact ⟨Int.natCast_nonneg b, by exact_mod_cast hb⟩
  · rw [hav, hev, Int.toNat_natCast]
    exact h

/-- `mem[a] := e ; s`, where a gives the address b, which lies in the memory, and e gives z. -/
theorem Ends.storeToThen {a e : Expr} {s : Stmt} (b : ℕ) (z : ℤ)
    (h : Ends lim P d s ⟨frame l, Function.update μ b z⟩ (T - (a.cost + e.cost + 1)) Q)
    (he : a.Gives lim ⟨frame l, μ⟩ b ∧ e.Gives lim ⟨frame l, μ⟩ z ∧ b < lim.space := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : a.cost + e.cost + 1 ≤ T := by first
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
    Ends lim P d ((Light.Stmt.seq (.store a e) s)) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.storeTo b z h he le_rfl) hT





























































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












@[simp] theorem Seg.nil : Seg μ a [] := fun i h => absurd h (by simp)






















































































































































































end Light

end
end

section


/-!
# Exact retained catalog and scratch interfaces for the level loop

These records collect the memory assertions already produced by the actual
prefix-catalog constructor. They contain no assumed query procedure. The
query adapter below invokes the existing closed, verified catalog program.
-/

namespace ThreeSum.ReportingHostLevelData

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false













variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]







































theorem Bounds.mono {h J k baseL baseR stop stop' : ℕ} {D : Catalog}
    (H : Bounds h J k D baseL baseR stop) (hle : stop≤stop') :
    Bounds h J k D baseL baseR stop' :=
  ⟨H.left.trans hle,H.right.trans hle,H.index.trans hle,H.pointers.trans hle,H.boxes.trans hle⟩





























theorem query_meets {lim : Limits} {μ : ℕ→ℤ} {h J k baseL baseR maskBase work depth : ℕ}
    {D : Catalog} (hk : k≤J) (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ) (w : Wanted h J α)
    (pre : List (Finset (Fin (512*h)))) (hp : ValidPrefix w.2.2 k pre)
    (hkey : w.1∈A ∧ globalModulus h J ∣ (a w.1%pMod+lift w.2.1*pMod+shift)-globalKey w.2.2)
    (hw : (lim.space : ℤ)≤lim.word)
    (HS : Sources μ pMod shift B C b c w.2.2 baseL baseR)
    (HC : Stored μ D hk pMod shift B C b c w.2.2)
    (HB : Bounds h J k D baseL baseR maskBase)
    (HW : Scratch lim h J k D B.card C.card maskBase work)
    (hd : depth+2*width h J+12≤lim.depth) :
    Meets lim LightReportingCatalogQuery.program 35 depth
      [width h J,sourceCut h J,suffixStage J (512*h) k,k*h,
        subsetMask (leftPrefix k (prefixRows (J := J) pre)),k*h,
        subsetMask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) pre)),
        suffixStage J (512*h) k,k*(512*h),residualSize h J k,subsetMask (querySet k (outputRows w.2.2)),
        D.t,baseL,baseR,D.boxCut,D.indexBase,D.ptrBase,count h k,maskBase,work]
      μ (LightReportingCatalogQuery.time h J k D.t)
      (fun r ν => r=(prefixQuery (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k pre : ℤ) ∧
        KeptBut μ ν work maskBase (LightSparseQuery.queryItems (residualSize h J k) D.t)) :=
  LightReportingCatalogQuery.program_meets pMod shift A B C a b c w pre hk hp hkey hw
    HB.left HB.right HB.index HB.pointers HB.boxes HW.masks HW.space HW.powers HW.emod
    HW.word HW.lookup HW.values HW.t HW.cut HW.flags HS.left HS.right HC.index HC.pointers HC.boxes hd

end ThreeSum.ReportingHostLevelData

end

section


/-! # Exact physical frontier slots and a capacity computed from root raw mass -/

namespace ThreeSum.ReportingHostFrontierLayout

open Light Finset ThreeSum.SubsetAddress
open BlockRows BlockIndex BlockIndexedQuery BlockForced StoredReporting GlobalEncoding LocalCoverBounds
open RawIncidences RawReporting LightBlockQuery ReportingHostMasks

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false





@[simp] theorem slot_zero (base cap : ℕ) : slot base cap 0=base := by simp [slot]
















@[simp] theorem left_zero {J L : ℕ} (u : Fin J→Finset (Fin L)) : leftPrefix 0 u=∅ := by
  ext x
  simp [leftPrefix,prefixLeft,prefixIndices,join,indexSet]

@[simp] theorem right_zero {J L : ℕ} (Q u : Fin J→Finset (Fin L)) : rightPrefix 0 Q u=∅ := by
  exact left_zero (fun i => Q i\u i)

@[simp] theorem query_zero {J L : ℕ} (Q : Fin J→Finset (Fin L)) :
    querySet 0 Q=indexSet (flat Q) := by
  simp [querySet,remaining,prefixIndices,flat]

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]











theorem group_pos (h : ℕ) : 0<groupSize h := Nat.choose_pos (by omega)

theorem capacity_pos {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) :
    0<capacity I w := Nat.mul_pos (by omega) (group_pos h)

theorem mass_lt_capacity {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) :
    rootMass I w<capacity I w :=
  (Nat.lt_succ_self _).trans_le (Nat.le_mul_of_pos_right _ (group_pos h))













theorem frontier_zero {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) :
    ReportingHostFrontier.frontier I w 0=if 0<rootMass I w then [[]] else [] := rfl













theorem leftMasks_zero {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) :
    leftMasks I w 0=if 0<rootMass I w then [0] else [] := by
  unfold leftMasks
  rw [frontier_zero]
  split <;> simp

theorem rightMasks_zero {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) :
    rightMasks I w 0=if 0<rootMass I w then [0] else [] := by
  unfold rightMasks
  rw [frontier_zero]
  split <;> simp

























end ThreeSum.ReportingHostFrontierLayout

end

section


/-!
# Actual root query and frontier initialization

The machine executes the exact catalog-backed empty-prefix query, computes
its capacity from the returned raw mass, and writes the root frontier and
its two aligned zero masks. No supplied root count or capacity is used.
-/

namespace ThreeSum.LightReportingInitialize

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockIndex BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog
open ReportingHostLevelData ReportingHostFrontierLayout

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

















variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem program_meets_sourceProof {μ : ℕ→ℤ} {h J baseL baseR maskBase work dst depth : ℕ} {D : Catalog}
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ) (w : Wanted h J α)
    (hkey : w.1∈A ∧ globalModulus h J ∣ (a w.1%pMod+lift w.2.1*pMod+shift)-globalKey w.2.2)
    (hw : (lim.space : ℤ)≤lim.word)
    (HS : Sources μ pMod shift B C b c w.2.2 baseL baseR)
    (HC : Stored μ D (Nat.zero_le J) pMod shift B C b c w.2.2)
    (HB : Bounds h J 0 D baseL baseR dst)
    (HW : Scratch lim h J 0 D B.card C.card maskBase work)
    (hout : slot dst (capacity (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w) 1≤maskBase)
    (hd : depth+2*width h J+13≤lim.depth) :
    Meets lim program 36 depth
      [width h J,sourceCut h J,suffixStage J (512*h) 0,0,0,0,0,suffixStage J (512*h) 0,0,
        residualSize h J 0,subsetMask (querySet 0 (outputRows w.2.2)),D.t,baseL,baseR,
        D.boxCut,D.indexBase,D.ptrBase,count h 0,maskBase,work,dst,groupSize h]
      μ (time h J D.t)
      (fun r ν =>
        let I := rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c
        r=((ReportingHostFrontier.frontier I w 0).length : ℤ) ∧
        At ν I w dst (capacity I w) 0 ∧
        ν (dst+2)=(rootMass I w : ℤ) ∧ ν (dst+3)=(capacity I w : ℤ) ∧ Kept μ ν dst) := by
  let I := rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c
  let cap := capacity I w
  change Meets lim program 36 depth _ μ (time h J D.t)
    (fun r ν => r=((ReportingHostFrontier.frontier I w 0).length : ℤ) ∧
      At ν I w dst cap 0 ∧ ν (dst+2)=(rootMass I w : ℤ) ∧ ν (dst+3)=(cap : ℤ) ∧ Kept μ ν dst)
  change slot dst cap 1≤maskBase at hout
  have hpos : 0<cap := capacity_pos I w
  have hmass : rootMass I w<cap := mass_lt_capacity I w
  have hout' : dst+4+2*cap≤maskBase := by simpa [slot,Nat.add_assoc] using hout
  have hmaskWork := HW.masks
  have hspace := HW.space
  have hcapSpace : cap≤lim.space := by omega
  have hcapWord : (cap : ℤ)≤lim.word := (Int.ofNat_le.mpr hcapSpace).trans hw
  have hrootWord : (rootMass I w : ℤ)≤lim.word := (Int.ofNat_le.mpr (hmass.le.trans hcapSpace)).trans hw
  have hmaskWord : (subsetMask (querySet 0 (outputRows w.2.2)) : ℤ)≤lim.word := by
    have hp : 2^(width h J)≤(width h J+1)*2^(width h J+1) :=
      (Nat.pow_le_pow_right (by decide) (by omega)).trans (Nat.le_mul_of_pos_left _ (by omega))
    exact (Int.ofNat_le.mpr ((subsetMask_isMask _).1.le.trans hp)).trans HW.word
  have hp : ValidPrefix w.2.2 0 [] := by simp [ValidPrefix]
  apply Meets.of_body (p := 36) (by rfl : program[36]?=some (body 35))
  unfold body time
  have he := (ReportingHostLevelData.query_meets (depth := depth+1) (Nat.zero_le J)
    pMod shift A B C a b c w [] hp hkey hw HS HC (HB.mono (by omega)) HW (by omega)).append [body 35]
  have hEmpty : subsetMask (∅ : Finset (Fin (width h J)))=0 := by rfl
  simp only [ReportingHostFrontierLayout.left_zero,ReportingHostFrontierLayout.right_zero,hEmpty,
    Nat.cast_zero,zero_mul] at he
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
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightReportingCatalogQuery.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightReportingCatalogQuery.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul,
                LightReportingCatalogQuery.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro mass ν ⟨hmassRet, hkept⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  change mass=(rootMass I w : ℤ) at hmassRet
  have hcapCalc : (mass+1)*(groupSize h : ℤ)=(cap : ℤ) := by
    rw [hmassRet]
    simp only [cap,capacity,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (cap : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hcapCalc, LightReportingCatalogQuery.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hcapCalc, LightReportingCatalogQuery.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hcapCalc,
                LightReportingCatalogQuery.time] <;>
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
    (refine Light.Ends.storeToThen (dst + 2) (rootMass I w : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hmassRet, LightReportingCatalogQuery.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hmassRet, LightReportingCatalogQuery.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hmassRet,
                LightReportingCatalogQuery.time] <;>
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
    (refine Light.Ends.storeToThen (dst + 3) (cap : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightReportingCatalogQuery.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightReportingCatalogQuery.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul,
                LightReportingCatalogQuery.time] <;>
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
        Light.Ends.storeToThen (dst + 1)
          (subsetMask (querySet 0 (outputRows w.2.2)) : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightReportingCatalogQuery.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightReportingCatalogQuery.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul,
                LightReportingCatalogQuery.time] <;>
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
    (refine Light.Ends.storeToThen (dst + 4) (0 : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightReportingCatalogQuery.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightReportingCatalogQuery.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul,
                LightReportingCatalogQuery.time] <;>
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
    (refine Light.Ends.storeToThen (dst + 4 + cap) (0 : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightReportingCatalogQuery.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightReportingCatalogQuery.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul,
                LightReportingCatalogQuery.time] <;>
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
        Light.Ends.iteIffThen ((0 : ℤ) < mass) (fun hyes => ?_) (fun hno => ?_) ?_
          ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightReportingCatalogQuery.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightReportingCatalogQuery.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul,
                LightReportingCatalogQuery.time] <;>
              omega)));
    (all_goals
        repeat
          with_unfolding_none
            first
            | refine Light.Ends.seqAssoc ?_
            | refine Light.Ends.skipThen ?_)
  · have hpositive : 0<rootMass I w := by omega
    have hfront : ReportingHostFrontier.frontier I w 0=[[]] := by rw [frontier_zero,if_pos hpositive]
    have hL : leftMasks I w 0=[0] := by rw [leftMasks_zero,if_pos hpositive]
    have hR : rightMasks I w 0=[0] := by rw [rightMasks_zero,if_pos hpositive]
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.storeToThen dst (1 : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  LightReportingCatalogQuery.time]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [LightReportingCatalogQuery.time] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul,
                  LightReportingCatalogQuery.time] <;>
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
      (refine Light.Ends.setToThen (1 : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  LightReportingCatalogQuery.time]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [LightReportingCatalogQuery.time] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul,
                  LightReportingCatalogQuery.time] <;>
                omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    refine ⟨by simp [hfront],?_,?_,?_,?_⟩
    · constructor
      · simp [slot,hfront]
      · simp [slot,Function.update_of_ne,show dst+1≠dst+4+cap by omega,show dst+1≠dst+4 by omega]
      · rw [hL]
        intro i hi
        have hz : i=0 := by simpa using hi
        subst i
        simp only [ReportingHostFrontierLayout.left,slot_zero,Nat.add_zero,
          Function.update_of_ne (show dst+4≠dst by omega),
          Function.update_of_ne (show dst+4≠dst+4+cap by omega),Function.update_self,List.map_cons,
          List.map_nil,List.getElem_cons_zero,Nat.cast_zero]
      · rw [hR]
        intro i hi
        have hz : i=0 := by simpa using hi
        subst i
        simp [ReportingHostFrontierLayout.right,ReportingHostFrontierLayout.left,slot,show dst+4+cap≠dst by omega]
    · simp [show dst+2≠dst by omega,show dst+2≠dst+4+cap by omega,show dst+2≠dst+4 by omega]
    · simp [show dst+3≠dst by omega,show dst+3≠dst+4+cap by omega,show dst+3≠dst+4 by omega]
    · intro i hi
      simp only [Function.update_of_ne (show i≠dst by omega),Function.update_of_ne (show i≠dst+4+cap by omega),
        Function.update_of_ne (show i≠dst+4 by omega),Function.update_of_ne (show i≠dst+1 by omega),
        Function.update_of_ne (show i≠dst+3 by omega),Function.update_of_ne (show i≠dst+2 by omega)]
      exact hkept i ⟨by omega,by omega⟩
  · have hzero : ¬0<rootMass I w := by omega
    have hfront : ReportingHostFrontier.frontier I w 0=[] := by rw [frontier_zero,if_neg hzero]
    have hL : leftMasks I w 0=[] := by rw [leftMasks_zero,if_neg hzero]
    have hR : rightMasks I w 0=[] := by rw [rightMasks_zero,if_neg hzero]
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.storeToThen dst (0 : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  LightReportingCatalogQuery.time]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [LightReportingCatalogQuery.time] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul,
                  LightReportingCatalogQuery.time] <;>
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
                  LightReportingCatalogQuery.time]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [LightReportingCatalogQuery.time] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul,
                  LightReportingCatalogQuery.time] <;>
                omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    refine ⟨by simp [hfront],?_,?_,?_,?_⟩
    · constructor
      · simp [slot,hfront]
      · simp [slot,Function.update_of_ne,show dst+1≠dst+4+cap by omega,show dst+1≠dst+4 by omega]
      · simp [hL,SegN]
      · simp [hR,SegN]
    · simp [show dst+2≠dst by omega,show dst+2≠dst+4+cap by omega,show dst+2≠dst+4 by omega]
    · simp [show dst+3≠dst by omega,show dst+3≠dst+4+cap by omega,show dst+3≠dst+4 by omega]
    · intro i hi
      simp only [Function.update_of_ne (show i≠dst by omega),Function.update_of_ne (show i≠dst+4+cap by omega),
        Function.update_of_ne (show i≠dst+4 by omega),Function.update_of_ne (show i≠dst+1 by omega),
        Function.update_of_ne (show i≠dst+3 by omega),Function.update_of_ne (show i≠dst+2 by omega)]
      exact hkept i ⟨by omega,by omega⟩

end ThreeSum.LightReportingInitialize

end

universe u_1 u_2 u_3

theorem solution : ∀ {lim : Light.Limits} {α : Type u_1} {β : Type u_2} {γ : Type u_3} [Fintype.{u_1} α] [Fintype.{u_2} β]
  [Fintype.{u_3} γ] [inst : DecidableEq.{u_1 + 1} α] [DecidableEq.{u_2 + 1} β] [DecidableEq.{u_3 + 1} γ] {μ : Nat → Int}
  {h J baseL baseR maskBase work dst depth : Nat} {D : ThreeSum.ReportingHostLevelData.Catalog} (pMod shift : Int)
  (A : Finset.{u_1} α) (B : Finset.{u_2} β) (C : Finset.{u_3} γ) (a : α → Int) (b : β → Int) (c : γ → Int)
  (w : ThreeSum.RawReporting.Wanted.{u_1} h J α),
  And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) A
        (@Prod.fst.{u_1, 0} α
          (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (ThreeSum.GlobalEncoding.GlobalOutput h J))
          w))
      (@Dvd.dvd.{0} Int Int.instDvd (ThreeSum.GlobalEncoding.globalModulus h J)
        (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
              (@HMod.hMod.{0, 0, 0} Int Int Int (@instHMod.{0} Int Int.instMod)
                (a
                  (@Prod.fst.{u_1, 0} α
                    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (ThreeSum.GlobalEncoding.GlobalOutput h J))
                    w))
                pMod)
              (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                (ThreeSum.RawIncidences.lift
                  (@Prod.fst.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (ThreeSum.GlobalEncoding.GlobalOutput h J)
                    (@Prod.snd.{u_1, 0} α
                      (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (ThreeSum.GlobalEncoding.GlobalOutput h J))
                      w)))
                pMod))
            shift)
          (@ThreeSum.GlobalEncoding.globalKey h J
            (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (ThreeSum.GlobalEncoding.GlobalOutput h J)
              (@Prod.snd.{u_1, 0} α
                (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (ThreeSum.GlobalEncoding.GlobalOutput h J))
                w))))) →
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
      @ThreeSum.ReportingHostLevelData.Sources.{u_2, u_3} β γ h J μ pMod shift B C b c
          (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (ThreeSum.GlobalEncoding.GlobalOutput h J)
            (@Prod.snd.{u_1, 0} α
              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput h J))
              w))
          baseL baseR →
        @ThreeSum.ReportingHostLevelData.Stored.{u_2, u_3} β γ h J
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) μ D (Nat.zero_le J) pMod shift B C b c
            (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (ThreeSum.GlobalEncoding.GlobalOutput h J)
              (@Prod.snd.{u_1, 0} α
                (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (ThreeSum.GlobalEncoding.GlobalOutput h J))
                w)) →
          ThreeSum.ReportingHostLevelData.Bounds h J (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) D
              baseL baseR dst →
            ThreeSum.ReportingHostLevelData.Scratch lim h J
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) D (@Finset.card.{u_2} β B)
                (@Finset.card.{u_3} γ C) maskBase work →
              @LE.le.{0} Nat instLENat
                  (ThreeSum.ReportingHostFrontierLayout.slot dst
                    (@ThreeSum.ReportingHostFrontierLayout.capacity.{u_1, u_2, u_3} α β γ inst h J
                      (@ThreeSum.RawIncidences.rawOn.{u_1, u_2, u_3} α β γ h J pMod shift
                        (@SProd.sprod.{u_1, max u_2 u_3, max (max u_1 u_2) u_3} (Finset.{u_1} α)
                          (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ))
                          (Finset.{max (max u_2 u_3) u_1} (Prod.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)))
                          (@Finset.instSProd.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)) A
                          (@SProd.sprod.{u_2, u_3, max u_2 u_3} (Finset.{u_2} β) (Finset.{u_3} γ)
                            (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ)) (@Finset.instSProd.{u_2, u_3} β γ) B C))
                        a b c)
                      w)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  maskBase →
                @LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          (ThreeSum.LightBlockQuery.width h J)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))))
                    lim.depth →
                  Light.Meets lim ThreeSum.LightReportingInitialize.program
                    (@OfNat.ofNat.{0} Nat (nat_lit 36) (instOfNatNat (nat_lit 36))) depth
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightBlockQuery.width h J))
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightBlockQuery.sourceCut h J))
                        (@List.cons.{0} Int
                          (@Nat.cast.{0} Int instNatCastInt
                            (ThreeSum.BlockIndexedQuery.suffixStage J
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                          (@List.cons.{0} Int (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                            (@List.cons.{0} Int (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                              (@List.cons.{0} Int (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons.{0} Int (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons.{0} Int
                                    (@Nat.cast.{0} Int instNatCastInt
                                      (ThreeSum.BlockIndexedQuery.suffixStage J
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                    (@List.cons.{0} Int (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons.{0} Int
                                        (@Nat.cast.{0} Int instNatCastInt
                                          (ThreeSum.LightBlockQuery.residualSize h J
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                        (@List.cons.{0} Int
                                          (@Nat.cast.{0} Int instNatCastInt
                                            (@ThreeSum.SubsetAddress.subsetMask
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                                              (@ThreeSum.BlockIndexedQuery.querySet J
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                                (@ThreeSum.BlockForced.outputRows h J
                                                  (@Prod.snd.{0, 0}
                                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                    (ThreeSum.GlobalEncoding.GlobalOutput h J)
                                                    (@Prod.snd.{u_1, 0} α
                                                      (Prod.{0, 0}
                                                        (Fin
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                        (ThreeSum.GlobalEncoding.GlobalOutput h J))
                                                      w))))))
                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt D.t)
                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt baseL)
                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt baseR)
                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt D.boxCut)
                                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt D.indexBase)
                                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt D.ptrBase)
                                                      (@List.cons.{0} Int
                                                        (@Nat.cast.{0} Int instNatCastInt
                                                          (ThreeSum.LightReportingPrefixCatalog.count h
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                              (instOfNatNat (nat_lit 0)))))
                                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt maskBase)
                                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
                                                              (@List.cons.{0} Int
                                                                (@Nat.cast.{0} Int instNatCastInt
                                                                  (ThreeSum.LocalCoverBounds.groupSize h))
                                                                (@List.nil.{0} Int)))))))))))))))))))))))
                    μ (ThreeSum.LightReportingInitialize.time h J D.t) fun (r : Int) (ν : Nat → Int) =>
                    have I :=
                      @ThreeSum.RawIncidences.rawOn.{u_1, u_2, u_3} α β γ h J pMod shift
                        (@SProd.sprod.{u_1, max u_2 u_3, max (max u_1 u_2) u_3} (Finset.{u_1} α)
                          (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ))
                          (Finset.{max (max u_2 u_3) u_1} (Prod.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)))
                          (@Finset.instSProd.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)) A
                          (@SProd.sprod.{u_2, u_3, max u_2 u_3} (Finset.{u_2} β) (Finset.{u_3} γ)
                            (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ)) (@Finset.instSProd.{u_2, u_3} β γ) B C))
                        a b c;
                    And
                      (@Eq.{1} Int r
                        (@Nat.cast.{0} Int instNatCastInt
                          (@List.length.{0}
                            (List.{0}
                              (Finset.{0}
                                (Fin
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
                            (@ThreeSum.ReportingHostFrontier.frontier.{u_1, u_2, u_3} α β γ inst h J I w
                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                      (And
                        (@ThreeSum.ReportingHostFrontierLayout.At.{u_1, u_2, u_3} α β γ inst h J ν I w dst
                          (@ThreeSum.ReportingHostFrontierLayout.capacity.{u_1, u_2, u_3} α β γ inst h J I w)
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (And
                          (@Eq.{1} Int
                            (ν
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (@Nat.cast.{0} Int instNatCastInt
                              (@ThreeSum.ReportingHostFrontierLayout.rootMass.{u_1, u_2, u_3} α β γ inst h J I w)))
                          (And
                            (@Eq.{1} Int
                              (ν
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              (@Nat.cast.{0} Int instNatCastInt
                                (@ThreeSum.ReportingHostFrontierLayout.capacity.{u_1, u_2, u_3} α β γ inst h J I w)))
                            (Light.Kept μ ν dst)))) := by
  exact @ThreeSum.LightReportingInitialize.program_meets_sourceProof

#print axioms solution
