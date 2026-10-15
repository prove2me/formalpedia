-- Prove2me | solution 1 for ThreeSum.LightDenseSetup.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:51:00.804695+00:00
-- url     : https://prove2.me/submissions/16d09083-2cc6-4c92-b478-94c789999fd0

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
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle14
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
import Theorems.Thm_ThreeSum_BandRawA_mem_aIndices_iff_owner
import Theorems.Thm_ThreeSum_BandRawA_mem_allProducts
import Theorems.Thm_ThreeSum_BandRawA_owner_weightedFalseCount
import Theorems.Thm_ThreeSum_BandWeightedScore_block_bound
import Theorems.Thm_ThreeSum_LightBandWeightedScore_program_meets
import Theorems.Thm_ThreeSum_LightCoverKeyData_Stored_of_kept
import Theorems.Thm_ThreeSum_LightNatPower_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
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
# The aggregate weighted score of physical band-owner candidates

Each flagged owner contributes the score of its three actual truncated
bands. Owner multiplicities are retained. The contraction and initial bound
therefore apply to the same quadratic catalog that the program scans.
-/

namespace ThreeSum.BandWeightedScore

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
































































theorem partialScore_bound (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) (k : ℕ)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j) :
    partialScore primes s q nA nB nC g A B C rs k ≤ k*(s*g^3) := by
  calc
    _ ≤ ∑ _i ∈ range k, s*g^3 := sum_le_sum fun i _ => block_bound primes s q nA nB nC g A B C _ hprime hinj
    _ = _ := by simp

theorem score_bound (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j) :
    score primes s q nA nB nC g A B C rs ≤ rs.length*(s*g^3) :=
  partialScore_bound primes s q nA nB nC g A B C rs rs.length hprime hinj


















































end ThreeSum.BandWeightedScore

end

section


/-!
# Each physical A incidence retains exactly its owner's B/C product

The products in this file are mathematical counting domains. The actual
catalog is still constructed by the verified quadratic owner loop and
linear band copies. Distinct owner products are disjoint because their
physical A incidence indices differ, even when their values coincide.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 1900000
set_option maxRecDepth 8000



























































theorem mem_ownerProduct {nA nB nC g s : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (hs : s < rs.length) :
    t ∈ ownerProduct nA nB nC g rs s ↔
      t.1 < (items nA g rs).length ∧ (labelAt nA g rs t.1).owner=s ∧
        t.2.1 ∈ bandPositions nB g (rs.getD s default).b ∧
        t.2.2 ∈ bandPositions nC g (rs.getD s default).c := by
  simp only [ownerProduct,mem_product,mem_aIndices_iff_owner hs,and_assoc]

theorem ownerProduct_disjoint {nA nB nC g s t : ℕ} {rs : List Record}
    (hs : s < rs.length) (ht : t < rs.length) (hst : s ≠ t) :
    Disjoint (ownerProduct nA nB nC g rs s) (ownerProduct nA nB nC g rs t) := by
  apply disjoint_left.mpr
  intro x hx hy
  have hs' := (mem_ownerProduct hs).mp hx
  have ht' := (mem_ownerProduct ht).mp hy
  exact hst (hs'.2.1.symm.trans ht'.2.1)
















































theorem sum_allProducts (F : (ℕ × ℕ × ℕ) → ℕ) (nA nB nC g : ℕ)
    (rs : List Record) :
    (∑ t ∈ allProducts nA nB nC g rs, F t)=
      ∑ s ∈ range rs.length, ∑ t ∈ ownerProduct nA nB nC g rs s, F t := by
  unfold allProducts
  apply sum_biUnion
  intro s hs t ht hst
  exact ownerProduct_disjoint (mem_range.mp hs) (mem_range.mp ht) hst





























end ThreeSum.BandRawA

end

section


/-!
# The aggregate prime score is the exact physical incidence-product score

The executable A catalog supplies the first-coordinate values. Its owner
metadata supplies the B/C slices. Thus the mathematical score summed by
the actual prime selector counts this same domain with all multiplicities.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 1900000
set_option maxRecDepth 8000







































theorem all_weightedFalseCount (primes : ℕ → ℕ) (aux q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) :
    Arithmetic.weightedFalseCount (allProducts nA nB nC g rs)
      (ModuloCounts.difference (valueAt nA g rs A) B C)
      (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux)) q=
      BandWeightedScore.score primes aux q nA nB nC g A B C rs := by
  unfold Arithmetic.weightedFalseCount
  rw [sum_allProducts]
  unfold BandWeightedScore.score BandWeightedScore.partialScore
  apply sum_congr rfl
  intro s hs
  exact owner_weightedFalseCount primes aux q nA nB nC g A B C rs (mem_range.mp hs)














































end ThreeSum.BandRawA

end

section


/-!
# Bounded finite index types for the same physical owner products

The A type is the complete flattened incidence array; B and C are the
retained sorted arrays. Coordinate transport is injective and preserves
both each owner's product and its exact weighted collision score.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000




















theorem coordinates_injective {a b c : ℕ} :
    Function.Injective (@coordinates a b c) := by
  rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ he
  simp only [coordinates,Prod.mk.injEq] at he
  exact Prod.ext (Fin.ext he.1) (Prod.ext (Fin.ext he.2.1) (Fin.ext he.2.2))

















@[simp] theorem mem_finiteAllProducts {nA nB nC g : ℕ} {rs : List Record}
    {t : Fin (items nA g rs).length × Fin nB × Fin nC} :
    t ∈ finiteAllProducts nA nB nC g rs ↔
      coordinates t ∈ allProducts nA nB nC g rs := by
  simp only [finiteAllProducts,mem_filter,mem_univ,true_and]













theorem allProducts_bounds {nA nB nC g : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ allProducts nA nB nC g rs) :
    t.1 < (items nA g rs).length ∧ t.2.1 < nB ∧ t.2.2 < nC := by
  obtain ⟨ha,hb,hc⟩ := mem_allProducts.mp ht
  exact ⟨ha,bandPositions_lt hb,bandPositions_lt hc⟩








theorem finite_lift {nA nB nC g : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ allProducts nA nB nC g rs) :
    ∃ u ∈ finiteAllProducts nA nB nC g rs, coordinates u=t := by
  obtain ⟨ha,hb,hc⟩ := allProducts_bounds ht
  refine ⟨(⟨t.1,ha⟩,⟨t.2.1,hb⟩,⟨t.2.2,hc⟩),?_,rfl⟩
  exact mem_finiteAllProducts.mpr ht
















theorem sum_finiteAllProducts (F : (ℕ × ℕ × ℕ) → ℕ) (nA nB nC g : ℕ)
    (rs : List Record) :
    (∑ u ∈ finiteAllProducts nA nB nC g rs, F (coordinates u))=
      ∑ t ∈ allProducts nA nB nC g rs, F t := by
  refine sum_bij (fun u _ => coordinates u) ?_ ?_ ?_ ?_
  · intro u hu
    exact mem_finiteAllProducts.mp hu
  · intro u hu v hv he
    exact coordinates_injective he
  · intro t ht
    obtain ⟨u,hu,he⟩ := finite_lift ht
    exact ⟨u,hu,he⟩
  · intro u hu
    rfl














theorem finiteAll_weightedFalseCount (primes : ℕ → ℕ) (aux q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) :
    Arithmetic.weightedFalseCount (finiteAllProducts nA nB nC g rs)
      (fun t => C t.2.2.val-B t.2.1.val-valueAt nA g rs A t.1.val)
      (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux)) q=
      BandWeightedScore.score primes aux q nA nB nC g A B C rs := by
  rw [← all_weightedFalseCount primes aux q nA nB nC g A B C rs]
  unfold Arithmetic.weightedFalseCount
  exact sum_finiteAllProducts
    (fun t => if (q : ℤ) ∣ ModuloCounts.difference (valueAt nA g rs A) B C t then
      Arithmetic.missWeight (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux))
        (ModuloCounts.difference (valueAt nA g rs A) B C t) else 0) nA nB nC g rs















end ThreeSum.BandRawA

end

section


/-!
# Scalar integer powers in the benchmark language

The exponent is a size parameter, so a loop of that many multiplications
has polynomial-logarithmic cost in the applications below. No power table
or auxiliary memory is required.
-/

namespace ThreeSum.LightNatPower

open Light

variable {lim : Limits} {P : Program} {d : ℕ}










































theorem bounded_meets {p b e : ℕ} (hp : P[p]? = some body) (μ : ℕ → ℤ)
    (he : (e : ℤ) ≤ lim.word)
    (hword : (((b+1)^(e+1) : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [b,e] μ (time e)
      (fun r μ' => r = ((b^e : ℕ) : ℤ) ∧ μ' = μ) := by
  apply meets hp μ he
  intro i hi
  have hbase := Nat.pow_le_pow_left (show b ≤ b+1 by omega) i
  have hexp : (b+1)^i ≤ (b+1)^(e+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hz : ((b^i : ℕ) : ℤ) ≤ (((b+1)^(e+1) : ℕ) : ℤ) := by
    exact_mod_cast hbase.trans hexp
  exact hz.trans hword










end ThreeSum.LightNatPower

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







theorem layer_end_le_header (free h J : ℕ) :
    LightCoverKeys.afterCover free h+outputCount (512*h) h ≤ LightCoverKeys.keyHeader free h J := by
  unfold LightCoverKeys.keyHeader LightGlobalKeys.scratch
  omega

theorem afterCover_le_keyEnd (free h J : ℕ) : LightCoverKeys.afterCover free h ≤ keyEnd free h J := by
  have hh := layer_end_le_header free h J
  unfold keyEnd
  omega






















































end ThreeSum.LightCoverKeyData

end

section


/-!
# Compute the representation cap from the actual retained cover

The two factors are read from the verified cover header. An actual scalar
power loop computes the J-fold cap; no cap value is supplied as an input.
-/

namespace ThreeSum.LightDenseCap

open Light GlobalEncoding LocalCoverBounds















theorem header_cap {μ : ℕ → ℤ} {free h J : ℕ}
    (H : LightCoverKeyData.Stored μ free h J) : μ (free+7)=(localBucketCap h : ℤ) := by
  have hv := H.header 7 (by simp [LightLocalCoverInit.values,LightLocalParameters.values,
    LightLocalCounts.values,LightLocalCoverMetadata.values])
  simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
    LightLocalCoverMetadata.values] using hv

theorem header_schedule {μ : ℕ → ℤ} {free h J : ℕ}
    (H : LightCoverKeyData.Stored μ free h J) : μ (free+10)=(scheduleSize h : ℤ) := by
  have hv := H.header 10 (by simp [LightLocalCoverInit.values,LightLocalParameters.values,
    LightLocalCounts.values,LightLocalCoverMetadata.values])
  simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
    LightLocalCoverMetadata.values] using hv








variable {lim : Limits} {P : Program} {μ : ℕ → ℤ} {free h J d : ℕ}

theorem meets {pMain pPower : ℕ} (hp : P[pMain]?=some (body pPower))
    (hPower : P[pPower]?=some LightNatPower.body)
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : free+11 ≤ lim.space)
    (hword : (word h J : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (H : LightCoverKeyData.Stored μ free h J) :
    Meets lim P pMain d [free,J] μ (time J)
      (fun result ν => result=(representationCap h J : ℤ) ∧ ν=μ) := by
  have budget (a : ℕ) (ha : a ≤ word h J) : (a : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ha).trans hword
  have hcap := budget (localBucketCap h) (by unfold word; omega)
  have hsq := budget (localBucketCap h^2) (by unfold word; omega)
  have hS := budget (scheduleSize h) (by unfold word; omega)
  have hb := budget (base h) (by unfold word; omega)
  have hJ := budget J (by unfold word; omega)
  have hpow := budget ((base h+1)^(J+1)) (by unfold word; omega)
  have hsqZ : (localBucketCap h : ℤ)*(localBucketCap h : ℤ) ≤ lim.word := by
    simpa only [Nat.cast_pow,pow_two,Nat.cast_mul] using hsq
  have hbZ : (scheduleSize h : ℤ)*(localBucketCap h : ℤ)^2 ≤ lim.word := by
    simpa only [base,Nat.cast_mul,Nat.cast_pow] using hb
  have hsqN : (0 : ℤ) ≤ (localBucketCap h : ℤ)*(localBucketCap h : ℤ) := by positivity
  have hbN : (0 : ℤ) ≤ (scheduleSize h : ℤ)*(localBucketCap h : ℤ)^2 := by positivity
  have hcapRead : μ (((free : ℤ)+7).toNat)=(localBucketCap h : ℤ) := by
    rw [show ((free : ℤ)+7).toNat=free+7 by omega]
    exact header_cap H
  have hSRead : μ (((free : ℤ)+10).toNat)=(scheduleSize h : ℤ) := by
    rw [show ((free : ℤ)+10).toNat=free+10 by omega]
    exact header_schedule H
  apply Meets.of_body hp
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
    (refine Light.Ends.setToThen (localBucketCap h : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hcapRead]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hcapRead] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hcapRead] <;> omega)));
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
    (refine Light.Ends.setToThen (scheduleSize h : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hSRead]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hSRead] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hSRead] <;> omega)));
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
    (refine Light.Ends.setToThen (localBucketCap h ^ 2 : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                pow_two]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [pow_two] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, pow_two] <;> omega)));
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
    (refine Light.Ends.setToThen (base h : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, base]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [base] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, base] <;> omega)));
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
    (first
      |
        refine
          Light.Ends.callToThen
            ((LightNatPower.bounded_meets (d := d + 1) hPower μ hJ hpow) _
              (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (LightNatPower.bounded_meets (d := d + 1) hPower μ hJ hpow) ?_ ?_ ?_
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
        ((rintro result ν ⟨hr, hν⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  exact ⟨hr,hν⟩



theorem program_meets (hw : (lim.space : ℤ) ≤ lim.word) (hspace : free+11 ≤ lim.space)
    (hword : (word h J : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (H : LightCoverKeyData.Stored μ free h J) :
    Meets lim program 0 d [free,J] μ (time J)
      (fun result ν => result=(representationCap h J : ℤ) ∧ ν=μ) :=
  meets rfl rfl hw hspace hword hd H

end ThreeSum.LightDenseCap

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
# Construct the dense-stop threshold from actual cover and source records

The host computes the representation cap, recomputes the exact aggregate
weighted score at the selected common modulus, multiplies the two, and
initializes the running counter. The four retained cells are counter,
threshold, representation cap and weighted score. Scratch starts after them.
-/

namespace ThreeSum.LightDenseSetup

open Light GlobalEncoding BandCandidateRows

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000




































theorem falseScore_eq (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) :
    falseScore primes s q nA nB nC g A B C rs=
      BandWeightedScore.score primes s q nA nB nC g A B C rs :=
  BandRawA.finiteAll_weightedFalseCount primes s q nA nB nC g A B C rs

variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs q aux s cover free maxMod U h J : ℕ}

theorem program_meets_sourceProof (primes : ℕ → ℕ) (rs : List Record)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+Nat.clog 2 maxMod+7 ≤ lim.depth)
    (hg : 0 < g) (hq : 0 < q) (hqmax : q ≤ maxMod)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hrecs : recs+4*rs.length ≤ free) (haux : aux+s ≤ free)
    (hcover : LightCoverKeyData.keyEnd cover h J ≤ free)
    (hspace : LightWeightedScore.space (free+4) maxMod g U ≤ lim.space)
    (hword : (word maxMod nA nB nC g rs.length s U h J : ℤ) ≤ lim.word)
    (H : LightCoverKeyData.Stored μ cover h J)
    (hrecords : Seg μ recs (cells rs))
    (hflag : ∀ r ∈ rs, r.flag=0 ∨ r.flag=1)
    (hvalid : ∀ r ∈ rs, r.flag=1 → r.a*g ≤ nA ∧ r.b*g ≤ nB ∧ r.c*g ≤ nC)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ))
    (hread : ∀ i < s, μ (aux+i)=(primes i : ℤ))
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j)
    (hproduct : ∀ i < s, q*primes i ≤ maxMod) :
    Meets lim program 19 d [a,b,c,nA,nB,nC,g,recs,rs.length,q,aux,s,cover,J,free] μ
      (time maxMod g rs.length s U J)
      (fun result ν => result=(free : ℤ) ∧
        Stored ν free (representationCap h J)
          (falseScore primes s q nA nB nC g
            (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) rs) ∧
        LightCoverKeyData.Stored ν cover h J ∧ Kept μ ν free) := by
  let score := BandWeightedScore.score primes s q nA nB nC g
    (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) rs
  have budget (x : ℕ) (hx : x ≤ word maxMod nA nB nC g rs.length s U h J) :
      (x : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hx).trans hword
  have hcapWord := budget (LightDenseCap.word h J) (by unfold word; omega)
  have hscoreWord := budget (LightBandWeightedScore.word maxMod nA nB nC g rs.length s U)
    (by unfold word; omega)
  have hcapFit := budget (representationCap h J) (by unfold word; omega)
  have hsBound : score ≤ rs.length*(s*g^3) :=
    BandWeightedScore.score_bound primes s q nA nB nC g _ _ _ rs hprime hinj
  have hthresholdFit : ((representationCap h J*score : ℕ) : ℤ) ≤ lim.word := by
    apply budget
    exact (Nat.mul_le_mul_left _ hsBound).trans (by unfold word; omega)
  have hthresholdZ : (representationCap h J : ℤ)*(score : ℤ) ≤ lim.word := by
    simpa only [Nat.cast_mul] using hthresholdFit
  have hthresholdN : (0 : ℤ) ≤ (representationCap h J : ℤ)*(score : ℤ) := by positivity
  have hscoreFit : (score : ℤ) ≤ lim.word := by
    apply budget
    apply hsBound.trans
    unfold word LightBandWeightedScore.word
    omega
  have hfree : free+4 ≤ lim.space := by
    have hh := (le_max_right _ _).trans hspace
    change free+4+(Nat.log 2 (maxMod+1)+2) ≤ lim.space at hh
    omega
  have hcoverBase := LightLocalCoverRetention.base_le_nextFree (LightLocalCoverInit.base cover) h
  change cover+20 ≤ LightCoverKeys.afterCover cover h at hcoverBase
  have hcoverNext := LightCoverKeyData.afterCover_le_keyEnd cover h J
  apply Meets.of_body (p := 19) (by rfl : program[19]?=some (body 0 18))
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
    (refine Light.Ends.setToThen (free + 4 : ℕ) ?_ ?_ ?_);
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
  have hcapCall := ((LightDenseCap.program_meets (d := d+1) (μ := μ)
    hw (by omega) hcapWord (by omega) H).append
      (LightBandWeightedScore.program.map (ReportingHostRelocation.relocate 2))).append [body 0 18]
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
      | refine Light.Ends.callToThen (hcapCall _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hcapCall ?_ ?_ ?_ ?_);
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
        ((rintro cap μ₁ ⟨hcap, hμ₁⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  subst μ₁
  have hscoreCall := (ReportingHostRelocation.meets
    (LightBandWeightedScore.program_meets (d := d+1) (μ := μ) (free := free+4)
      primes rs hw (by omega) hg hq hqmax (by omega) (by omega) (by omega)
      (by omega) (by omega) hspace hscoreWord hrecords hflag hvalid hA hB hC
      hread hprime hinj hproduct) LightDenseCap.program).append [body 0 18]
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
      | refine Light.Ends.callToThen (hscoreCall _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hscoreCall ?_ ?_ ?_ ?_);
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
        ((rintro total μ₂ ⟨hscore, hkeep⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have htotal : total=(score : ℤ) := hscore
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (representationCap h J * score : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hcap,
                htotal]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hcap, htotal] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hcap, htotal] <;> omega)));
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
    (refine Light.Ends.storeToThen free (0 : ℕ) ?_ ?_ ?_);
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
    (refine
        Light.Ends.storeToThen (free + 1) (representationCap h J * score : ℕ) ?_
          ?_ ?_);
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
    (refine
        Light.Ends.storeToThen (free + 2) (representationCap h J : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hcap]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hcap] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hcap] <;> omega)));
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
    (refine Light.Ends.storeToThen (free + 3) (score : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                htotal]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [htotal] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, htotal] <;> omega)));
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
    (refine Light.Ends.setToThen (free : ℕ) ?_ ?_ ?_);
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
  refine ⟨rfl,?_,?_,?_⟩
  · exact ⟨by simp,by simp [score,falseScore_eq],by simp,by simp [score,falseScore_eq]⟩
  · apply H.of_kept
    intro i hi
    change Function.update (Function.update (Function.update (Function.update μ₂ free _)
      (free+1) _) (free+2) _) (free+3) _ i=μ i
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),
      Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    exact hkeep i (by omega)
  · intro i hi
    change Function.update (Function.update (Function.update (Function.update μ₂ free _)
      (free+1) _) (free+2) _) (free+3) _ i=μ i
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),
      Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    exact hkeep i (by omega)

end ThreeSum.LightDenseSetup

end


theorem solution : ∀ {lim : Light.Limits} {d : Nat} {μ : Nat → Int} {a b c nA nB nC g recs q aux s cover free maxMod U h J : Nat}
  (primes : Nat → Nat) (rs : List.{0} ThreeSum.BandCandidateRows.Record),
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
            (Nat.clog (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) maxMod))
          (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
        lim.depth →
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) g →
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q →
          @LE.le.{0} Nat instLENat q maxMod →
            @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a nA) free →
              @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b nB) free →
                @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c nC) free →
                  @LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) recs
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                          (@List.length.{0} ThreeSum.BandCandidateRows.Record rs)))
                      free →
                    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) aux s)
                        free →
                      @LE.le.{0} Nat instLENat (ThreeSum.LightCoverKeyData.keyEnd cover h J) free →
                        @LE.le.{0} Nat instLENat
                            (ThreeSum.LightWeightedScore.space
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) free
                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                              maxMod g U)
                            lim.space →
                          @LE.le.{0} Int Int.instLEInt
                              (@Nat.cast.{0} Int instNatCastInt
                                (ThreeSum.LightDenseSetup.word maxMod nA nB nC g
                                  (@List.length.{0} ThreeSum.BandCandidateRows.Record rs) s U h J))
                              lim.word →
                            ThreeSum.LightCoverKeyData.Stored μ cover h J →
                              Light.Seg μ recs (ThreeSum.BandCandidateRows.cells rs) →
                                (∀ (r : ThreeSum.BandCandidateRows.Record),
                                    @Membership.mem.{0, 0} ThreeSum.BandCandidateRows.Record
                                        (List.{0} ThreeSum.BandCandidateRows.Record)
                                        (@List.instMembership.{0} ThreeSum.BandCandidateRows.Record) rs r →
                                      Or
                                        (@Eq.{1} Nat r.flag
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                        (@Eq.{1} Nat r.flag
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                  (∀ (r : ThreeSum.BandCandidateRows.Record),
                                      @Membership.mem.{0, 0} ThreeSum.BandCandidateRows.Record
                                          (List.{0} ThreeSum.BandCandidateRows.Record)
                                          (@List.instMembership.{0} ThreeSum.BandCandidateRows.Record) rs r →
                                        @Eq.{1} Nat r.flag
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                                          And
                                            (@LE.le.{0} Nat instLENat
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) r.a g)
                                              nA)
                                            (And
                                              (@LE.le.{0} Nat instLENat
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) r.b g)
                                                nB)
                                              (@LE.le.{0} Nat instLENat
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) r.c g)
                                                nC))) →
                                    (∀ (i : Nat),
                                        @LT.lt.{0} Nat instLTNat i nA →
                                          @LE.le.{0} Int Int.instLEInt
                                            (@abs.{0} Int instLatticeInt Int.instAddGroup
                                              (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a i)))
                                            (@Nat.cast.{0} Int instNatCastInt U)) →
                                      (∀ (i : Nat),
                                          @LT.lt.{0} Nat instLTNat i nB →
                                            @LE.le.{0} Int Int.instLEInt
                                              (@abs.{0} Int instLatticeInt Int.instAddGroup
                                                (μ
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b
                                                    i)))
                                              (@Nat.cast.{0} Int instNatCastInt U)) →
                                        (∀ (i : Nat),
                                            @LT.lt.{0} Nat instLTNat i nC →
                                              @LE.le.{0} Int Int.instLEInt
                                                (@abs.{0} Int instLatticeInt Int.instAddGroup
                                                  (μ
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c
                                                      i)))
                                                (@Nat.cast.{0} Int instNatCastInt U)) →
                                          (∀ (i : Nat),
                                              @LT.lt.{0} Nat instLTNat i s →
                                                @Eq.{1} Int
                                                  (μ
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) aux
                                                      i))
                                                  (@Nat.cast.{0} Int instNatCastInt (primes i))) →
                                            (∀ (i : Nat), @LT.lt.{0} Nat instLTNat i s → Nat.Prime (primes i)) →
                                              (∀ (i : Nat),
                                                  @LT.lt.{0} Nat instLTNat i s →
                                                    ∀ (j : Nat),
                                                      @LT.lt.{0} Nat instLTNat j s →
                                                        @Eq.{1} Nat (primes i) (primes j) → @Eq.{1} Nat i j) →
                                                (∀ (i : Nat),
                                                    @LT.lt.{0} Nat instLTNat i s →
                                                      @LE.le.{0} Nat instLENat
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          q (primes i))
                                                        maxMod) →
                                                  Light.Meets lim ThreeSum.LightDenseSetup.program
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19))) d
                                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
                                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt b)
                                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt c)
                                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt nA)
                                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt nB)
                                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt nC)
                                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt g)
                                                                  (@List.cons.{0} Int
                                                                    (@Nat.cast.{0} Int instNatCastInt recs)
                                                                    (@List.cons.{0} Int
                                                                      (@Nat.cast.{0} Int instNatCastInt
                                                                        (@List.length.{0}
                                                                          ThreeSum.BandCandidateRows.Record rs))
                                                                      (@List.cons.{0} Int
                                                                        (@Nat.cast.{0} Int instNatCastInt q)
                                                                        (@List.cons.{0} Int
                                                                          (@Nat.cast.{0} Int instNatCastInt aux)
                                                                          (@List.cons.{0} Int
                                                                            (@Nat.cast.{0} Int instNatCastInt s)
                                                                            (@List.cons.{0} Int
                                                                              (@Nat.cast.{0} Int instNatCastInt cover)
                                                                              (@List.cons.{0} Int
                                                                                (@Nat.cast.{0} Int instNatCastInt J)
                                                                                (@List.cons.{0} Int
                                                                                  (@Nat.cast.{0} Int instNatCastInt
                                                                                    free)
                                                                                  (@List.nil.{0} Int))))))))))))))))
                                                    μ
                                                    (ThreeSum.LightDenseSetup.time maxMod g
                                                      (@List.length.{0} ThreeSum.BandCandidateRows.Record rs) s U J)
                                                    fun (result : Int) (ν : Nat → Int) =>
                                                    And (@Eq.{1} Int result (@Nat.cast.{0} Int instNatCastInt free))
                                                      (And
                                                        (ThreeSum.LightDenseSetup.Stored ν free
                                                          (ThreeSum.GlobalEncoding.representationCap h J)
                                                          (ThreeSum.LightDenseSetup.falseScore primes s q nA nB nC g
                                                            (fun (i : Nat) =>
                                                              μ
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat) a i))
                                                            (fun (i : Nat) =>
                                                              μ
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat) b i))
                                                            (fun (i : Nat) =>
                                                              μ
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat) c i))
                                                            rs))
                                                        (And (ThreeSum.LightCoverKeyData.Stored ν cover h J)
                                                          (Light.Kept μ ν free))) := by
  exact @ThreeSum.LightDenseSetup.program_meets_sourceProof

#print axioms solution
