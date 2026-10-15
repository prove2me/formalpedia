-- Prove2me | solution 1 for ThreeSum.LightSourceBandBanks.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T17:42:03.388987+00:00
-- url     : https://prove2.me/submissions/dfbe6ac2-4f1e-4610-a8f6-84e2d9abf586

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
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
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
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
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
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_LightSourceBandBanks_afterCount_ends


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.SourceBandBankData
end ThreeSum.SourceBandBankData
namespace ThreeSum.SourceBandBankLayout
end ThreeSum.SourceBandBankLayout
namespace ThreeSum.SourceBandLayout
end ThreeSum.SourceBandLayout
namespace ThreeSum.SourceBandPairData
end ThreeSum.SourceBandPairData
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# Consecutive bands of a strictly increasing array

The last band is truncated. Every input position belongs to its quotient
band, the bands are strictly separated, and each band has at most `g` entries.
The quotient in these specifications is realized by `LightBandPartition`.
-/

namespace ThreeSum.BandPartition





theorem size_le (n g : ℕ) : size n g ≤ n := by
  unfold size
  split_ifs with h
  · omega
  · have hdiv := Nat.div_le_self (n-1) g
    omega
































































































end ThreeSum.BandPartition

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








/-- A piece of the program about which `h` is known, at the end of the program. -/
theorem Ends.pieceLast {σ : State} {T T₁ : ℕ} {s : Stmt} {R Q : State → Prop}
    (h : Ends lim P d s σ T₁ R) (rest : ∀ σ', R σ' → Q σ') (hT : T₁ ≤ T := by first
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
    Ends lim P d s σ T Q :=
  h.mono hT rest







































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























end

/-! ## The rule for calls -/

section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : State → Prop} {s : Stmt}











































end

end Light

end
end

section


/-!
# Original-input histograms give the exact independently trimmed sources

The histogram keys retain the first modular reduction and the signed carry
offset. Looking up the endpoint's final residue therefore counts precisely
the original divisibility condition in `BlockEncoding`. An explicit finite
enumeration accounts for every original input incidence once.
-/

namespace ThreeSum.BlockSourceEncoding

open Finset BlockEncoding GlobalEncoding LocalCoverBounds LightSourceResidues
open scoped BigOperators

set_option maxHeartbeats 1000000





































@[simp] theorem modulus_cast (h J : ℕ) : (modulus h J : ℤ) = globalModulus h J := by
  simp only [modulus,globalModulus,Nat.cast_pow]

section OriginalSources

variable {β : Type*} [DecidableEq β]



























end OriginalSources

end ThreeSum.BlockSourceEncoding

end

section


/-! # Two retained original-band catalogs and one shared empty histogram -/

namespace ThreeSum.SourceBandPairData

open Light BandPartition






theorem work_ge (base n g m : ℕ) : base ≤ SourceBandLayout.work base n g m := by
  unfold SourceBandLayout.work SourceBandLayout.hist SourceBandLayout.data
  omega

theorem ordered (base NL NR g m : ℕ) :
    leftBase base ≤ rightBase base NL g m ∧
    rightBase base NL g m ≤ zeroBase base NL NR g m ∧
    zeroBase base NL NR g m < next base NL NR g m := by
  exact ⟨work_ge _ _ _ _,work_ge _ _ _ _,by unfold next; omega⟩










































































end ThreeSum.SourceBandPairData

end

section


/-! # Padded histogram selection for independently chosen original bands -/

namespace ThreeSum.SourceBandPairSlices

open Light BandPartition SourceBandLayout SourceBandPairData





















































theorem heads_read {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g p m : ℕ} {shift : ℤ}
    (H : Stored μ fL fR base NL NR g p m shift) :
    μ base=(leftBase base : ℤ) ∧ μ (base+1)=(size NL g : ℤ) ∧
    μ (base+2)=(rightBase base NL g m : ℤ) ∧ μ (base+3)=(size NR g : ℤ) ∧
    μ (base+4)=(zeroBase base NL NR g m : ℤ) ∧ μ (base+5)=(next base NL NR g m : ℤ) ∧
    μ (base+6)=(NL : ℤ) ∧ μ (base+7)=(NR : ℤ) := by
  exact ⟨by simpa [header] using H.heads.getD (i := 0) (by simp [header]) 0,
    by simpa [header] using H.heads.getD (i := 1) (by simp [header]) 0,
    by simpa [header] using H.heads.getD (i := 2) (by simp [header]) 0,
    by simpa [header] using H.heads.getD (i := 3) (by simp [header]) 0,
    by simpa [header] using H.heads.getD (i := 4) (by simp [header]) 0,
    by simpa [header] using H.heads.getD (i := 5) (by simp [header]) 0,
    by simpa [header] using H.heads.getD (i := 6) (by simp [header]) 0,
    by simpa [header] using H.heads.getD (i := 7) (by simp [header]) 0⟩

end ThreeSum.SourceBandPairSlices

end

section


/-!
# One occurrence catalog reused across all original source bands

The physical B/C band counts determine the loop length. A single radix
decoder loop constructs the occurrence rows. The bank loop then selects
retained histograms and builds exactly two families per common band and
occurrence. The result header stores the first bank base, band count, band
stride, next free address, and occurrence-row pointer.
-/

namespace ThreeSum.LightSourceBandBanks

open Light GlobalEncoding BlockEncoding BlockCoefficientRows BlockSourceEncoding
open LocalCoverBounds SubsetAddress BlockSourceOccurrenceOrder SourceBandBankLayout SourceBandBankData

set_option maxHeartbeats 4000000
set_option maxRecDepth 18000














































variable {lim : Limits} {P : Program} {d : ℕ}






































































































theorem Procs.meets_sourceProof {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {pair NL NR g p h J cut occ maps candidates histL histR base : ℕ}
    {shift : ℤ} (H : SourceBandPairData.Stored μ fL fR pair NL NR g p (modulus h J) shift)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+14 ≤ lim.depth)
    (hg : 0 < g) (hcut : cut ≤ J*(512*h))
    (hpair : SourceBandPairData.next pair NL NR g (modulus h J) ≤ occ)
    (hocc : occ+LightBlockSourceCatalog.count h J*J ≤ base)
    (hmaps : maps+2*(512*h)*scheduleSize h ≤ occ)
    (hcandidates : candidates+scheduleSize h ≤ occ)
    (hleft : histL+LightLocalCoverSchedule.rows h*localPrime h ≤ occ)
    (hright : histR+LightLocalCoverSchedule.rows h*localPrime h ≤ occ)
    (hspace : space base NL NR g h J cut ≤ lim.space)
    (hword : (word NL NR h J : ℤ) ≤ lim.word)
    (hcover : BlockSourceCoverInput.Input μ h maps candidates histL histR) :
    Meets lim P pMain d
      [J,512*h,h,localPrime h,localBucketCap h,cut,modulus h J,occ,maps,candidates,histL,histR,
        pair,base,downsetCap (J*(512*h)) cut,LightBlockSourceCatalog.count h J,scheduleSize h,span h J cut]
      μ (time NL NR g h J cut) (fun r ν =>
        r=(finish base NL NR g h J cut : ℤ) ∧
        Stored ν fL fR base NL NR g h J cut occ (p : ℤ) shift ∧ Kept μ ν occ) := by
  obtain ⟨_,hcountL,_,hcountR,_⟩ := SourceBandPairSlices.heads_read H
  have hsRows : LightOutputDecodeDigits.space (finish base NL NR g h J cut) (LightBlockSourceCatalog.count h J) ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hs : finish base NL NR g h J cut ≤ lim.space := by unfold LightOutputDecodeDigits.space at hsRows; omega
  have hfirst : first base ≤ finish base NL NR g h J cut := Nat.le_add_right _ _
  have hbaseSpace : base+5 ≤ lim.space := hfirst.trans hs
  have ho := SourceBandPairData.ordered pair NL NR g (modulus h J)
  have hhead : pair+8 ≤ base := by unfold SourceBandPairData.leftBase at ho; omega
  have hwBanks : (LightSourceBandBankStep.word NL NR h J : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_left _ _)).trans hword
  have hNL := BandPartition.size_le NL g
  have hNR := BandPartition.size_le NR g
  have hcountWordL : (BandPartition.size NL g : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show BandPartition.size NL g ≤ LightSourceBandBankStep.word NL NR h J by
      unfold LightSourceBandBankStep.word; omega)).trans hwBanks
  have hcountWordR : (BandPartition.size NR g : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show BandPartition.size NR g ≤ LightSourceBandBankStep.word NL NR h J by
      unfold LightSourceBandBankStep.word; omega)).trans hwBanks
  have h32 : (32 : ℤ) ≤ lim.word := by unfold LightSourceBandBankStep.word at hwBanks; omega
  have haddr1 : ((pair : ℤ)+1).toNat=pair+1 := by omega
  have haddr3 : ((pair : ℤ)+3).toNat=pair+3 := by omega
  have htime : afterTime NL NR g h J cut=
      LightSourceOccurrenceArray.time (LightBlockSourceCatalog.count h J) J+
        LightSourceBandBankBatch.time NL NR g h J cut+1000 := rfl
  apply Meets.of_body C.main
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
    (refine Light.Ends.setToThen (BandPartition.size NL g : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hcountL,
                haddr1]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hcountL, haddr1] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hcountL, haddr1] <;>
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
        Light.Ends.iteIffThen
          ((BandPartition.size NL g : ℤ) < (BandPartition.size NR g : ℤ))
          (fun hy => ?_) (fun hn => ?_) ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hcountR,
                haddr3]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hcountR, haddr3] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hcountR, haddr3] <;>
              omega)));
    (all_goals
        repeat
          with_unfolding_none
            first
            | refine Light.Ends.seqAssoc ?_
            | refine Light.Ends.skipThen ?_)
  · have hK : BandPartition.size NR g=SourceBandPairSlices.count NL NR g := by
      unfold SourceBandPairSlices.count
      omega
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (BandPartition.size NR g : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hcountR,
                  haddr3]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hcountR, haddr3] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hcountR, haddr3] <;>
                omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    focus
      ((refine
            Light.Ends.pieceLast
              (afterCount_ends C.rows C.digits C.divide C.banks H hw hd hg hcut hK
                hpair hocc hmaps hcandidates hleft hright hspace hword hcover)
              (fun _ apspMacro_29998_0 => apspMacro_29998_0) ?_);
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
                  | ((ring_nf); (omega)))))
  · have hK : BandPartition.size NL g=SourceBandPairSlices.count NL NR g := by
      unfold SourceBandPairSlices.count
      omega
    focus
      ((refine
            Light.Ends.pieceLast
              (afterCount_ends C.rows C.digits C.divide C.banks H hw hd hg hcut hK
                hpair hocc hmaps hcandidates hleft hright hspace hword hcover)
              (fun _ apspMacro_30284_0 => apspMacro_30284_0) ?_);
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
                  | ((ring_nf); (omega)))))

end ThreeSum.LightSourceBandBanks

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (C : ThreeSum.LightSourceBandBanks.Procs P pMain)
  {μ fL fR : Nat → Int} {pair NL NR g p h J cut occ maps candidates histL histR base : Nat} {shift : Int},
  ThreeSum.SourceBandPairData.Stored μ fL fR pair NL NR g p (ThreeSum.BlockSourceEncoding.modulus h J) shift →
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
      @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
            (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
          lim.depth →
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) g →
          @LE.le.{0} Nat instLENat cut
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)) →
            @LE.le.{0} Nat instLENat
                (ThreeSum.SourceBandPairData.next pair NL NR g (ThreeSum.BlockSourceEncoding.modulus h J)) occ →
              @LE.le.{0} Nat instLENat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) occ
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (ThreeSum.LightBlockSourceCatalog.count h J) J))
                  base →
                @LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                        (ThreeSum.GlobalEncoding.scheduleSize h)))
                    occ →
                  @LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) candidates
                        (ThreeSum.GlobalEncoding.scheduleSize h))
                      occ →
                    @LE.le.{0} Nat instLENat
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histL
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (ThreeSum.LightLocalCoverSchedule.rows h) (ThreeSum.LocalCoverBounds.localPrime h)))
                        occ →
                      @LE.le.{0} Nat instLENat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histR
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (ThreeSum.LightLocalCoverSchedule.rows h) (ThreeSum.LocalCoverBounds.localPrime h)))
                          occ →
                        @LE.le.{0} Nat instLENat (ThreeSum.LightSourceBandBanks.space base NL NR g h J cut) lim.space →
                          @LE.le.{0} Int Int.instLEInt
                              (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightSourceBandBanks.word NL NR h J))
                              lim.word →
                            ThreeSum.BlockSourceCoverInput.Input μ h maps candidates histL histR →
                              Light.Meets lim P pMain d
                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt J)
                                  (@List.cons.{0} Int
                                    (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                                      (@OfNat.ofNat.{0} Int (nat_lit 512) (@instOfNat (nat_lit 512)))
                                      (@Nat.cast.{0} Int instNatCastInt h))
                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt h)
                                      (@List.cons.{0} Int
                                        (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LocalCoverBounds.localPrime h))
                                        (@List.cons.{0} Int
                                          (@Nat.cast.{0} Int instNatCastInt
                                            (ThreeSum.LocalCoverBounds.localBucketCap h))
                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cut)
                                            (@List.cons.{0} Int
                                              (@Nat.cast.{0} Int instNatCastInt
                                                (ThreeSum.BlockSourceEncoding.modulus h J))
                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt occ)
                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt maps)
                                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt candidates)
                                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt histL)
                                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt histR)
                                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt pair)
                                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt base)
                                                            (@List.cons.{0} Int
                                                              (@Nat.cast.{0} Int instNatCastInt
                                                                (ThreeSum.SubsetAddress.downsetCap
                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                    (@instHMul.{0} Nat instMulNat) J
                                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                      (@instHMul.{0} Nat instMulNat)
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                                        (instOfNatNat (nat_lit 512)))
                                                                      h))
                                                                  cut))
                                                              (@List.cons.{0} Int
                                                                (@Nat.cast.{0} Int instNatCastInt
                                                                  (ThreeSum.LightBlockSourceCatalog.count h J))
                                                                (@List.cons.{0} Int
                                                                  (@Nat.cast.{0} Int instNatCastInt
                                                                    (ThreeSum.GlobalEncoding.scheduleSize h))
                                                                  (@List.cons.{0} Int
                                                                    (@Nat.cast.{0} Int instNatCastInt
                                                                      (ThreeSum.SourceBandBankLayout.span h J cut))
                                                                    (@List.nil.{0} Int)))))))))))))))))))
                                μ (ThreeSum.LightSourceBandBanks.time NL NR g h J cut) fun (r : Int) (ν : Nat → Int) =>
                                And
                                  (@Eq.{1} Int r
                                    (@Nat.cast.{0} Int instNatCastInt
                                      (ThreeSum.SourceBandBankData.finish base NL NR g h J cut)))
                                  (And
                                    (ThreeSum.SourceBandBankData.Stored ν fL fR base NL NR g h J cut occ
                                      (@Nat.cast.{0} Int instNatCastInt p) shift)
                                    (Light.Kept μ ν occ)) := by
  exact @ThreeSum.LightSourceBandBanks.Procs.meets_sourceProof

#print axioms solution
