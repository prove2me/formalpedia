-- Prove2me | solution 1 for ThreeSum.LightReportingLeafBatch.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:33:04.19809+00:00
-- url     : https://prove2.me/submissions/55fcb782-b7f5-4328-ba5f-ce58fef220eb

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
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
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
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
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
import Theorems.Thm_ThreeSum_LightReportingLeaf_program_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.ReportingHostBucketTest
end ThreeSum.ReportingHostBucketTest
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets

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




theorem SameOn.refl : SameOn K μ μ := fun _ _ => rfl


















/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}














































/-! ## The tactics -/









































end Light

end
end

section


/-!
# A linear-time histogram procedure in the benchmark language

The input is an array of already computed residue indices in `[0,p)`.
The output is cleared and incremented once per input item. Multiplicities
are retained, including repeated equal residues.
-/

namespace ThreeSum.LightHistogram

open Light Finset

variable {lim : Limits} {P : Program} {d : ℕ}










theorem count_succ (key : ℕ → ℕ) (r i : ℕ) :
    count key r (i + 1) = count key r i + if key i = r then 1 else 0 := by
  unfold count
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases heq : key i = r
  · rw [if_pos heq, Finset.card_insert_of_notMem (by simp)]
    simp [heq]
  · simp [heq]





























































































end ThreeSum.LightHistogram

end

section


/-!
# Exact positions of original indices in retained residue buckets

Counting-sort positions preserve every input incidence. The resulting fiber
segments contain no repeated physical indices even when input values agree.
All inverse-enumeration reasoning is semantic; the actual scatter program
writes these positions using a cursor and never searches an input band.
-/

namespace ThreeSum.SourceBuckets

open Finset LightHistogram

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000






theorem offset_succ (key : ℕ → ℕ) (N r : ℕ) :
    offset key N (r+1) = offset key N r+count key r N := by
  exact Finset.sum_range_succ _ _

theorem offset_mono (key : ℕ → ℕ) (N : ℕ) : Monotone (offset key N) := by
  intro r s hrs
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hrs)

theorem count_mono (key : ℕ → ℕ) (r : ℕ) : Monotone (count key r) := by
  intro i j hij
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hij))

theorem count_strict {key : ℕ → ℕ} {r i j : ℕ} (hij : i < j) (hkey : key i = r) :
    count key r i < count key r j := by
  have he := count_succ key r i
  simp only [hkey,ite_true] at he
  have hm := count_mono key r (show i+1 ≤ j by omega)
  omega

theorem offset_total {key : ℕ → ℕ} {N M : ℕ} (hkey : ∀ i < N, key i < M) :
    offset key N M = N := by
  unfold offset count
  have he := Finset.card_eq_sum_card_fiberwise
    (f := key) (s := range N) (t := range M)
    (fun i hi => Finset.mem_range.mpr (hkey i (Finset.mem_range.mp hi)))
  simpa only [Finset.card_range] using he.symm

theorem offset_le {key : ℕ → ℕ} {N M r : ℕ} (hkey : ∀ i < N, key i < M) (hr : r ≤ M) :
    offset key N r ≤ N := by
  exact (offset_mono key N hr).trans_eq (offset_total hkey)






theorem position_end {key : ℕ → ℕ} {N i : ℕ} (hi : i < N) :
    position key N i < offset key N (key i+1) := by
  rw [offset_succ]
  exact Nat.add_lt_add_left (count_strict hi rfl) _

theorem position_lt {key : ℕ → ℕ} {N M i : ℕ} (hkey : ∀ i < N, key i < M) (hi : i < N) :
    position key N i < N :=
  (position_end hi).trans_le (offset_le hkey (by have hk := hkey i hi; omega))























































































































end ThreeSum.SourceBuckets

end

section


/-!
# Executable residue selection and original-value leaf decision

The host reduces the two actual endpoint values, selects the independently
trimmed physical buckets, and tests original values. Its Boolean result has
a memory-independent physical-index specification, suitable for sequential
candidate batching with the exact sum of the selected pair costs.
-/

namespace ThreeSum.LightReportingLeaf

open Light SourceBuckets LightResidues ReportingHostBucketTest

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000


















theorem stored_of_kept {μ ν : ℕ→ℤ} {key : ℕ→ℕ} {N Mo offsets flat stop : ℕ}
    (H : Stored μ key N Mo offsets flat) (hkey : ∀ i<N, key i<Mo)
    (hoffsets : offsets+Mo+1≤stop) (hflat : flat+N≤stop) (hkeep : Kept μ ν stop) :
    Stored ν key N Mo offsets flat := by
  constructor
  · intro r hr
    exact (hkeep _ (by omega)).trans (H.offsets r hr)
  · intro i hi
    have hpos := position_lt hkey hi
    exact (hkeep _ (by omega)).trans (H.indices i hi)

variable {lim : Limits}


















































































end ThreeSum.LightReportingLeaf

end

section


/-!
# Actual terminal-candidate batch with a sum of physical pair charges

All endpoint and independent flag arrays are read from retained memory.
The recursion evaluates each candidate and retains a Boolean disjunction.
Its cost sums the actual leaf costs instead of multiplying a worst fiber
size by the number of candidates.
-/

namespace ThreeSum.LightReportingLeafBatch

open Light Finset SourceBuckets LightResidues
open scoped BigOperators

set_option maxHeartbeats 2600000
set_option maxRecDepth 10000





theorem hit_succ (a : ℤ) (xL xR left right : ℕ→ℤ) (keyL keyR flagL flagR : ℕ→ℕ)
    (NL NR Mo n : ℕ) :
    Hit a xL xR left right keyL keyR flagL flagR NL NR Mo (n+1) ↔
      Hit a xL xR left right keyL keyR flagL flagR NL NR Mo n ∨
      LightReportingLeaf.Hit a (xL n) (xR n) left right keyL keyR NL NR Mo (flagL n) (flagR n) := by
  constructor
  · rintro ⟨i,hi,hh⟩
    by_cases hin : i<n
    · exact Or.inl ⟨i,hin,hh⟩
    · have he : i=n := by omega
      exact Or.inr (he ▸ hh)
  · rintro (⟨i,hi,hh⟩ | hh)
    · exact ⟨i,by omega,hh⟩
    · exact ⟨n,by omega,hh⟩





























variable {lim : Limits}

theorem program_meets_sourceProof {μ : ℕ→ℤ}
    {srcL srcR offsetsL offsetsR flatL flatR NL NR Mo rawL rawR flagsL flagsR n work U d : ℕ}
    (a : ℤ) (xL xR left right : ℕ→ℤ) (keyL keyR flagL flagR : ℕ→ℕ)
    (HL : Stored μ keyL NL Mo offsetsL flatL) (HR : Stored μ keyR NR Mo offsetsR flatR)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+n+4≤lim.depth) (hMo : 0<Mo)
    (hsrcL : srcL+NL≤work) (hsrcR : srcR+NR≤work)
    (hoffsetsL : offsetsL+Mo+1≤work) (hoffsetsR : offsetsR+Mo+1≤work)
    (hflatL : flatL+NL≤work) (hflatR : flatR+NR≤work)
    (hrawL : rawL+n≤work) (hrawR : rawR+n≤work)
    (hflagsL : flagsL+n≤work) (hflagsR : flagsR+n≤work)
    (hspace : work+4+(Nat.log 2 (U+1)+2)≤lim.space)
    (hword : (4*U+4*Mo+16 : ℤ)≤lim.word)
    (hkeyL : ∀ i<NL, keyL i<Mo) (hkeyR : ∀ j<NR, keyR j<Mo)
    (hflagL : ∀ i<n, flagL i≤1) (hflagR : ∀ i<n, flagR i≤1)
    (hreadL : ∀ i<NL, μ (srcL+i)=left i) (hreadR : ∀ j<NR, μ (srcR+j)=right j)
    (hreadXL : ∀ i<n, μ (rawL+i)=xL i) (hreadXR : ∀ i<n, μ (rawR+i)=xR i)
    (hreadFL : ∀ i<n, μ (flagsL+i)=(flagL i : ℤ))
    (hreadFR : ∀ i<n, μ (flagsR+i)=(flagR i : ℤ))
    (hvaluesL : ∀ i<NL, |left i|≤lim.word) (hvaluesR : ∀ j<NR, |right j|≤lim.word)
    (ha : |a|≤lim.word) (htarget : ∀ i<NL, |a+left i|≤lim.word)
    (hxL : ∀ i<n, |xL i|≤(U : ℤ)) (hxR : ∀ i<n, |xR i|≤(U : ℤ))
    (hcountWord : ((NL*NR : ℕ) : ℤ)≤lim.word) :
    Meets lim program 6 d [a,srcL,srcR,offsetsL,flatL,offsetsR,flatR,NL,NR,Mo,rawL,rawR,flagsL,flagsR,n,work]
      μ (time keyL keyR flagL flagR NL NR Mo U xL xR n)
      (fun r ν => (r=0 ∨ r=1) ∧ (r=1 ↔ Hit a xL xR left right keyL keyR flagL flagR NL NR Mo n) ∧
        Kept μ ν work) := by
  have haBounds := abs_le.mp ha
  induction n generalizing μ d with
  | zero =>
      apply Meets.of_body (p := 6) (by rfl : program[6]?=some (body 6 5))
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
            Light.Ends.iteIffThen ((0 : ℤ) < 0) (fun hbad => ?_) (fun hno => ?_) ?_
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
        (all_goals
            repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)
      · omega
      · focus
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
        exact ⟨by simp,by simp [Hit],SameOn.refl⟩
  | succ n ih =>
      apply Meets.of_body (p := 6) (by rfl : program[6]?=some (body 6 5))
      unfold body
      rw [time]
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
            Light.Ends.iteIffThen ((0 : ℤ) < ((n + 1 : ℕ) : ℤ)) (fun hyes => ?_)
              (fun hbad => ?_) ?_ ?_);
        (on_goal -1 =>
            first
            |
              ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                    LightReportingLeaf.time, LightReportingBucketTest.time,
                    LightReportingBucketPairs.time, residueBudget]);
                (first
                  | omega
                  | ((ring_nf); (omega))))
            | omega
            |
              (simp [LightReportingLeaf.time, LightReportingBucketTest.time,
                    LightReportingBucketPairs.time, residueBudget] <;>
                  first
                  | omega
                  | ((ring_nf); (omega))));
        (on_goal -1 =>
            (((try have := Light.Std.space_le (by assumption)));
              ((try have := Light.Std.const_le (by assumption)));
              (simp [Light.Limits.Addr, abs_le, -abs_mul, LightReportingLeaf.time,
                    LightReportingBucketTest.time, LightReportingBucketPairs.time,
                    residueBudget] <;>
                  omega)));
        (all_goals
            repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)
      · have hrun := ih (μ := μ) (d := d+1) HL HR (by omega)
          (by omega) (by omega) (by omega) (by omega)
          (fun i hi => hflagL i (by omega)) (fun i hi => hflagR i (by omega))
          hreadL hreadR (fun i hi => hreadXL i (by omega)) (fun i hi => hreadXR i (by omega))
          (fun i hi => hreadFL i (by omega)) (fun i hi => hreadFR i (by omega))
          (fun i hi => hxL i (by omega)) (fun i hi => hxR i (by omega))
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
            | refine Light.Ends.callToThen (hrun _ (by omega)) ?_ ?_ ?_ ?_
            | refine Light.Ends.callToThen hrun ?_ ?_ ?_ ?_);
          (on_goal -1 =>
              first
              |
                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                      LightReportingLeaf.time, LightReportingBucketTest.time,
                      LightReportingBucketPairs.time, residueBudget]);
                  (first
                    | omega
                    | ((ring_nf); (omega))))
              | omega
              |
                (simp [LightReportingLeaf.time, LightReportingBucketTest.time,
                      LightReportingBucketPairs.time, residueBudget] <;>
                    first
                    | omega
                    | ((ring_nf); (omega))));
          (on_goal -1 => omega);
          (on_goal -1 =>
              (((try have := Light.Std.space_le (by assumption)));
                ((try have := Light.Std.const_le (by assumption)));
                (simp [Light.Limits.Addr, abs_le, -abs_mul, LightReportingLeaf.time,
                      LightReportingBucketTest.time, LightReportingBucketPairs.time,
                      residueBudget] <;>
                    omega)));
          (on_goal -1 =>
              ((rintro prev ν ⟨hprevBool, hprev, hkeep⟩);
                (try with_unfolding_none refine Light.Ends.skip ?_)))
        have HLν := LightReportingLeaf.stored_of_kept HL hkeyL hoffsetsL hflatL hkeep
        have HRν := LightReportingLeaf.stored_of_kept HR hkeyR hoffsetsR hflatR hkeep
        have hxL' := abs_le.mp (hxL n (by omega))
        have hxR' := abs_le.mp (hxR n (by omega))
        have hfL := hflagL n (by omega)
        have hfR := hflagR n (by omega)
        have hXL : ν (rawL+n)=xL n := (hkeep _ (by omega)).trans (hreadXL n (by omega))
        have hXR : ν (rawR+n)=xR n := (hkeep _ (by omega)).trans (hreadXR n (by omega))
        have hFL : ν (flagsL+n)=(flagL n : ℤ) := (hkeep _ (by omega)).trans (hreadFL n (by omega))
        have hFR : ν (flagsR+n)=(flagR n : ℤ) := (hkeep _ (by omega)).trans (hreadFR n (by omega))
        focus
          ((((first
                  | refine Light.Ends.seqSelf ?_
                  | refine Light.Ends.skipLast ?_));
              (repeat
                  with_unfolding_none
                    first
                    | refine Light.Ends.seqAssoc ?_
                    | refine Light.Ends.skipThen ?_)));
          (refine Light.Ends.setToThen (n : ℕ) ?_ ?_ ?_);
          (on_goal -1 =>
              first
              |
                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                      LightReportingLeaf.time, LightReportingBucketTest.time,
                      LightReportingBucketPairs.time, residueBudget]);
                  (first
                    | omega
                    | ((ring_nf); (omega))))
              | omega
              |
                (simp [LightReportingLeaf.time, LightReportingBucketTest.time,
                      LightReportingBucketPairs.time, residueBudget] <;>
                    first
                    | omega
                    | ((ring_nf); (omega))));
          (on_goal -1 =>
              (((try have := Light.Std.space_le (by assumption)));
                ((try have := Light.Std.const_le (by assumption)));
                (simp [Light.Limits.Addr, abs_le, -abs_mul, LightReportingLeaf.time,
                      LightReportingBucketTest.time, LightReportingBucketPairs.time,
                      residueBudget] <;>
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
          (refine Light.Ends.setToThen (xL n) ?_ ?_ ?_);
          (on_goal -1 =>
              first
              |
                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hXL,
                      LightReportingLeaf.time, LightReportingBucketTest.time,
                      LightReportingBucketPairs.time, residueBudget]);
                  (first
                    | omega
                    | ((ring_nf); (omega))))
              | omega
              |
                (simp [hXL, LightReportingLeaf.time, LightReportingBucketTest.time,
                      LightReportingBucketPairs.time, residueBudget] <;>
                    first
                    | omega
                    | ((ring_nf); (omega))));
          (on_goal -1 =>
              (((try have := Light.Std.space_le (by assumption)));
                ((try have := Light.Std.const_le (by assumption)));
                (simp [Light.Limits.Addr, abs_le, -abs_mul, hXL,
                      LightReportingLeaf.time, LightReportingBucketTest.time,
                      LightReportingBucketPairs.time, residueBudget] <;>
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
          (refine Light.Ends.setToThen (xR n) ?_ ?_ ?_);
          (on_goal -1 =>
              first
              |
                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hXR,
                      LightReportingLeaf.time, LightReportingBucketTest.time,
                      LightReportingBucketPairs.time, residueBudget]);
                  (first
                    | omega
                    | ((ring_nf); (omega))))
              | omega
              |
                (simp [hXR, LightReportingLeaf.time, LightReportingBucketTest.time,
                      LightReportingBucketPairs.time, residueBudget] <;>
                    first
                    | omega
                    | ((ring_nf); (omega))));
          (on_goal -1 =>
              (((try have := Light.Std.space_le (by assumption)));
                ((try have := Light.Std.const_le (by assumption)));
                (simp [Light.Limits.Addr, abs_le, -abs_mul, hXR,
                      LightReportingLeaf.time, LightReportingBucketTest.time,
                      LightReportingBucketPairs.time, residueBudget] <;>
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
          (refine Light.Ends.setToThen (flagL n : ℕ) ?_ ?_ ?_);
          (on_goal -1 =>
              first
              |
                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hFL,
                      LightReportingLeaf.time, LightReportingBucketTest.time,
                      LightReportingBucketPairs.time, residueBudget]);
                  (first
                    | omega
                    | ((ring_nf); (omega))))
              | omega
              |
                (simp [hFL, LightReportingLeaf.time, LightReportingBucketTest.time,
                      LightReportingBucketPairs.time, residueBudget] <;>
                    first
                    | omega
                    | ((ring_nf); (omega))));
          (on_goal -1 =>
              (((try have := Light.Std.space_le (by assumption)));
                ((try have := Light.Std.const_le (by assumption)));
                (simp [Light.Limits.Addr, abs_le, -abs_mul, hFL,
                      LightReportingLeaf.time, LightReportingBucketTest.time,
                      LightReportingBucketPairs.time, residueBudget] <;>
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
          (refine Light.Ends.setToThen (flagR n : ℕ) ?_ ?_ ?_);
          (on_goal -1 =>
              first
              |
                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hFR,
                      LightReportingLeaf.time, LightReportingBucketTest.time,
                      LightReportingBucketPairs.time, residueBudget]);
                  (first
                    | omega
                    | ((ring_nf); (omega))))
              | omega
              |
                (simp [hFR, LightReportingLeaf.time, LightReportingBucketTest.time,
                      LightReportingBucketPairs.time, residueBudget] <;>
                    first
                    | omega
                    | ((ring_nf); (omega))));
          (on_goal -1 =>
              (((try have := Light.Std.space_le (by assumption)));
                ((try have := Light.Std.const_le (by assumption)));
                (simp [Light.Limits.Addr, abs_le, -abs_mul, hFR,
                      LightReportingLeaf.time, LightReportingBucketTest.time,
                      LightReportingBucketPairs.time, residueBudget] <;>
                    omega)));
          (try with_unfolding_none refine Light.Ends.skip ?_)
        have hleaf := (LightReportingLeaf.program_meets (μ := ν) (d := d+1) (srcL := srcL) (srcR := srcR)
          a (xL n) (xR n) left right keyL keyR HLν HRν hw (by omega) hMo
          hsrcL hsrcR hoffsetsL hoffsetsR hflatL hflatR hspace hword hkeyL hkeyR hfL hfR
          (fun i hi => (hkeep _ (by omega)).trans (hreadL i hi))
          (fun i hi => (hkeep _ (by omega)).trans (hreadR i hi))
          hvaluesL hvaluesR ha htarget (hxL n (by omega)) (hxR n (by omega)) hcountWord).append [body 6 5]
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
            | refine Light.Ends.callToThen (hleaf _ (by omega)) ?_ ?_ ?_ ?_
            | refine Light.Ends.callToThen hleaf ?_ ?_ ?_ ?_);
          (on_goal -1 =>
              first
              |
                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                      LightReportingLeaf.time, LightReportingBucketTest.time,
                      LightReportingBucketPairs.time, residueBudget]);
                  (first
                    | omega
                    | ((ring_nf); (omega))))
              | omega
              |
                (simp [LightReportingLeaf.time, LightReportingBucketTest.time,
                      LightReportingBucketPairs.time, residueBudget] <;>
                    first
                    | omega
                    | ((ring_nf); (omega))));
          (on_goal -1 => omega);
          (on_goal -1 =>
              (((try have := Light.Std.space_le (by assumption)));
                ((try have := Light.Std.const_le (by assumption)));
                (simp [Light.Limits.Addr, abs_le, -abs_mul, LightReportingLeaf.time,
                      LightReportingBucketTest.time, LightReportingBucketPairs.time,
                      residueBudget] <;>
                    omega)));
          (on_goal -1 =>
              ((rintro found ν₂ ⟨hfoundBool, hfound, hkeepLeaf⟩);
                (try with_unfolding_none refine Light.Ends.skip ?_)))
        have hprevRange : 0≤prev ∧ prev≤1 := by rcases hprevBool with h | h <;> omega
        have hfoundRange : 0≤found ∧ found≤1 := by rcases hfoundBool with h | h <;> omega
        have hwhole : Kept μ ν₂ work := fun i hi => (hkeepLeaf i hi).trans (hkeep i hi)
        have hsum : (0 : ℤ)<prev+found ↔ Hit a xL xR left right keyL keyR flagL flagR NL NR Mo (n+1) := by
          rw [hit_succ]
          rw [show (0 : ℤ)<prev+found ↔ prev=1 ∨ found=1 by omega,hprev,hfound]
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
              Light.Ends.iteIffThen ((0 : ℤ) < prev + found) (fun hfoundSome => ?_)
                (fun hfoundNone => ?_) ?_ ?_);
          (on_goal -1 =>
              first
              |
                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                      LightReportingLeaf.time, LightReportingBucketTest.time,
                      LightReportingBucketPairs.time, residueBudget]);
                  (first
                    | omega
                    | ((ring_nf); (omega))))
              | omega
              |
                (simp [LightReportingLeaf.time, LightReportingBucketTest.time,
                      LightReportingBucketPairs.time, residueBudget] <;>
                    first
                    | omega
                    | ((ring_nf); (omega))));
          (on_goal -1 =>
              (((try have := Light.Std.space_le (by assumption)));
                ((try have := Light.Std.const_le (by assumption)));
                (simp [Light.Limits.Addr, abs_le, -abs_mul, LightReportingLeaf.time,
                      LightReportingBucketTest.time, LightReportingBucketPairs.time,
                      residueBudget] <;>
                    omega)));
          (all_goals
              repeat
                with_unfolding_none
                  first
                  | refine Light.Ends.seqAssoc ?_
                  | refine Light.Ends.skipThen ?_)
        · have htrue := hsum.mp hfoundSome
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
                        LightReportingLeaf.time, LightReportingBucketTest.time,
                        LightReportingBucketPairs.time, residueBudget]);
                    (first
                      | omega
                      | ((ring_nf); (omega))))
                | omega
                |
                  (simp [LightReportingLeaf.time, LightReportingBucketTest.time,
                        LightReportingBucketPairs.time, residueBudget] <;>
                      first
                      | omega
                      | ((ring_nf); (omega))));
            (on_goal -1 =>
                (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, LightReportingLeaf.time,
                        LightReportingBucketTest.time, LightReportingBucketPairs.time,
                        residueBudget] <;>
                      omega)));
            (try with_unfolding_none refine Light.Ends.skip ?_)
          exact ⟨by simp,by simpa using htrue,hwhole⟩
        · have hfalse : ¬Hit a xL xR left right keyL keyR flagL flagR NL NR Mo (n+1) :=
            fun hh => hfoundNone (hsum.mpr hh)
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
                        LightReportingLeaf.time, LightReportingBucketTest.time,
                        LightReportingBucketPairs.time, residueBudget]);
                    (first
                      | omega
                      | ((ring_nf); (omega))))
                | omega
                |
                  (simp [LightReportingLeaf.time, LightReportingBucketTest.time,
                        LightReportingBucketPairs.time, residueBudget] <;>
                      first
                      | omega
                      | ((ring_nf); (omega))));
            (on_goal -1 =>
                (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, LightReportingLeaf.time,
                        LightReportingBucketTest.time, LightReportingBucketPairs.time,
                        residueBudget] <;>
                      omega)));
            (try with_unfolding_none refine Light.Ends.skip ?_)
          exact ⟨by simp,by simp [hfalse],hwhole⟩
      · omega

end ThreeSum.LightReportingLeafBatch

end


theorem solution : ∀ {lim : Light.Limits} {μ : Nat → Int}
  {srcL srcR offsetsL offsetsR flatL flatR NL NR Mo rawL rawR flagsL flagsR n work U d : Nat} (a : Int)
  (xL xR left right : Nat → Int) (keyL keyR flagL flagR : Nat → Nat),
  ThreeSum.SourceBuckets.Stored μ keyL NL Mo offsetsL flatL →
    ThreeSum.SourceBuckets.Stored μ keyR NR Mo offsetsR flatR →
      @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
        @LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d n)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            lim.depth →
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) Mo →
            @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcL NL) work →
              @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcR NR) work →
                @LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offsetsL Mo)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    work →
                  @LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offsetsR Mo)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      work →
                    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flatL NL)
                        work →
                      @LE.le.{0} Nat instLENat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flatR NR) work →
                        @LE.le.{0} Nat instLENat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rawL n) work →
                          @LE.le.{0} Nat instLENat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rawR n) work →
                            @LE.le.{0} Nat instLENat
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flagsL n) work →
                              @LE.le.{0} Nat instLENat
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flagsR n) work →
                                @LE.le.{0} Nat instLENat
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (Nat.log (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) U
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                    lim.space →
                                  @LE.le.{0} Int Int.instLEInt
                                      (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                                        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                                          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                                            (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4)))
                                            (@Nat.cast.{0} Int instNatCastInt U))
                                          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                                            (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4)))
                                            (@Nat.cast.{0} Int instNatCastInt Mo)))
                                        (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                                      lim.word →
                                    (∀ (i : Nat),
                                        @LT.lt.{0} Nat instLTNat i NL → @LT.lt.{0} Nat instLTNat (keyL i) Mo) →
                                      (∀ (j : Nat),
                                          @LT.lt.{0} Nat instLTNat j NR → @LT.lt.{0} Nat instLTNat (keyR j) Mo) →
                                        (∀ (i : Nat),
                                            @LT.lt.{0} Nat instLTNat i n →
                                              @LE.le.{0} Nat instLENat (flagL i)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                          (∀ (i : Nat),
                                              @LT.lt.{0} Nat instLTNat i n →
                                                @LE.le.{0} Nat instLENat (flagR i)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                            (∀ (i : Nat),
                                                @LT.lt.{0} Nat instLTNat i NL →
                                                  @Eq.{1} Int
                                                    (μ
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        srcL i))
                                                    (left i)) →
                                              (∀ (j : Nat),
                                                  @LT.lt.{0} Nat instLTNat j NR →
                                                    @Eq.{1} Int
                                                      (μ
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          srcR j))
                                                      (right j)) →
                                                (∀ (i : Nat),
                                                    @LT.lt.{0} Nat instLTNat i n →
                                                      @Eq.{1} Int
                                                        (μ
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) rawL i))
                                                        (xL i)) →
                                                  (∀ (i : Nat),
                                                      @LT.lt.{0} Nat instLTNat i n →
                                                        @Eq.{1} Int
                                                          (μ
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat) rawR i))
                                                          (xR i)) →
                                                    (∀ (i : Nat),
                                                        @LT.lt.{0} Nat instLTNat i n →
                                                          @Eq.{1} Int
                                                            (μ
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat) flagsL i))
                                                            (@Nat.cast.{0} Int instNatCastInt (flagL i))) →
                                                      (∀ (i : Nat),
                                                          @LT.lt.{0} Nat instLTNat i n →
                                                            @Eq.{1} Int
                                                              (μ
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat) flagsR i))
                                                              (@Nat.cast.{0} Int instNatCastInt (flagR i))) →
                                                        (∀ (i : Nat),
                                                            @LT.lt.{0} Nat instLTNat i NL →
                                                              @LE.le.{0} Int Int.instLEInt
                                                                (@abs.{0} Int instLatticeInt Int.instAddGroup (left i))
                                                                lim.word) →
                                                          (∀ (j : Nat),
                                                              @LT.lt.{0} Nat instLTNat j NR →
                                                                @LE.le.{0} Int Int.instLEInt
                                                                  (@abs.{0} Int instLatticeInt Int.instAddGroup
                                                                    (right j))
                                                                  lim.word) →
                                                            @LE.le.{0} Int Int.instLEInt
                                                                (@abs.{0} Int instLatticeInt Int.instAddGroup a)
                                                                lim.word →
                                                              (∀ (i : Nat),
                                                                  @LT.lt.{0} Nat instLTNat i NL →
                                                                    @LE.le.{0} Int Int.instLEInt
                                                                      (@abs.{0} Int instLatticeInt Int.instAddGroup
                                                                        (@HAdd.hAdd.{0, 0, 0} Int Int Int
                                                                          (@instHAdd.{0} Int Int.instAdd) a (left i)))
                                                                      lim.word) →
                                                                (∀ (i : Nat),
                                                                    @LT.lt.{0} Nat instLTNat i n →
                                                                      @LE.le.{0} Int Int.instLEInt
                                                                        (@abs.{0} Int instLatticeInt Int.instAddGroup
                                                                          (xL i))
                                                                        (@Nat.cast.{0} Int instNatCastInt U)) →
                                                                  (∀ (i : Nat),
                                                                      @LT.lt.{0} Nat instLTNat i n →
                                                                        @LE.le.{0} Int Int.instLEInt
                                                                          (@abs.{0} Int instLatticeInt Int.instAddGroup
                                                                            (xR i))
                                                                          (@Nat.cast.{0} Int instNatCastInt U)) →
                                                                    @LE.le.{0} Int Int.instLEInt
                                                                        (@Nat.cast.{0} Int instNatCastInt
                                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                            (@instHMul.{0} Nat instMulNat) NL NR))
                                                                        lim.word →
                                                                      Light.Meets lim
                                                                        ThreeSum.LightReportingLeafBatch.program
                                                                        (@OfNat.ofNat.{0} Nat (nat_lit 6)
                                                                          (instOfNatNat (nat_lit 6)))
                                                                        d
                                                                        (@List.cons.{0} Int a
                                                                          (@List.cons.{0} Int
                                                                            (@Nat.cast.{0} Int instNatCastInt srcL)
                                                                            (@List.cons.{0} Int
                                                                              (@Nat.cast.{0} Int instNatCastInt srcR)
                                                                              (@List.cons.{0} Int
                                                                                (@Nat.cast.{0} Int instNatCastInt
                                                                                  offsetsL)
                                                                                (@List.cons.{0} Int
                                                                                  (@Nat.cast.{0} Int instNatCastInt
                                                                                    flatL)
                                                                                  (@List.cons.{0} Int
                                                                                    (@Nat.cast.{0} Int instNatCastInt
                                                                                      offsetsR)
                                                                                    (@List.cons.{0} Int
                                                                                      (@Nat.cast.{0} Int instNatCastInt
                                                                                        flatR)
                                                                                      (@List.cons.{0} Int
                                                                                        (@Nat.cast.{0} Int
                                                                                          instNatCastInt NL)
                                                                                        (@List.cons.{0} Int
                                                                                          (@Nat.cast.{0} Int
                                                                                            instNatCastInt NR)
                                                                                          (@List.cons.{0} Int
                                                                                            (@Nat.cast.{0} Int
                                                                                              instNatCastInt Mo)
                                                                                            (@List.cons.{0} Int
                                                                                              (@Nat.cast.{0} Int
                                                                                                instNatCastInt rawL)
                                                                                              (@List.cons.{0} Int
                                                                                                (@Nat.cast.{0} Int
                                                                                                  instNatCastInt rawR)
                                                                                                (@List.cons.{0} Int
                                                                                                  (@Nat.cast.{0} Int
                                                                                                    instNatCastInt
                                                                                                    flagsL)
                                                                                                  (@List.cons.{0} Int
                                                                                                    (@Nat.cast.{0} Int
                                                                                                      instNatCastInt
                                                                                                      flagsR)
                                                                                                    (@List.cons.{0} Int
                                                                                                      (@Nat.cast.{0} Int
                                                                                                        instNatCastInt
                                                                                                        n)
                                                                                                      (@List.cons.{0}
                                                                                                        Int
                                                                                                        (@Nat.cast.{0}
                                                                                                          Int
                                                                                                          instNatCastInt
                                                                                                          work)
                                                                                                        (@List.nil.{0}
                                                                                                          Int)))))))))))))))))
                                                                        μ
                                                                        (ThreeSum.LightReportingLeafBatch.time keyL keyR
                                                                          flagL flagR NL NR Mo U xL xR n)
                                                                        fun (r : Int) (ν : Nat → Int) =>
                                                                        And
                                                                          (Or
                                                                            (@Eq.{1} Int r
                                                                              (@OfNat.ofNat.{0} Int (nat_lit 0)
                                                                                (@instOfNat (nat_lit 0))))
                                                                            (@Eq.{1} Int r
                                                                              (@OfNat.ofNat.{0} Int (nat_lit 1)
                                                                                (@instOfNat (nat_lit 1)))))
                                                                          (And
                                                                            (Iff
                                                                              (@Eq.{1} Int r
                                                                                (@OfNat.ofNat.{0} Int (nat_lit 1)
                                                                                  (@instOfNat (nat_lit 1))))
                                                                              (ThreeSum.LightReportingLeafBatch.Hit a xL
                                                                                xR left right keyL keyR flagL flagR NL
                                                                                NR Mo n))
                                                                            (Light.Kept μ ν work)) := by
  exact @ThreeSum.LightReportingLeafBatch.program_meets_sourceProof

#print axioms solution
