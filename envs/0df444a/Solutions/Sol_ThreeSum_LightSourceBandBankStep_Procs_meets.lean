-- Prove2me | solution 1 for ThreeSum.LightSourceBandBankStep.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T17:17:37.381439+00:00
-- url     : https://prove2.me/submissions/9b8b5fba-fe20-43f8-a9d3-ff9e8424ebce

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
import Definitions.Def_ThreeSum1962Source_Bundle13
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
import Theorems.Thm_ThreeSum_BlockSourceCoverInput_Input_of_kept
import Theorems.Thm_ThreeSum_LightBlockSourceBatch_Procs_meets
import Theorems.Thm_ThreeSum_LightSourceBandHistSelect_meets
import Theorems.Thm_ThreeSum_SourceBandPairData_Stored_of_kept


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
namespace ThreeSum.BlockSourceSharing
end ThreeSum.BlockSourceSharing
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LightZetaStages
end ThreeSum.LightZetaStages
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SourceBandLayout
end ThreeSum.SourceBandLayout
namespace ThreeSum.SourceBandPairData
end ThreeSum.SourceBandPairData
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales

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









































theorem length_le (n g i : ℕ) : stop n g i-start g i ≤ g := by
  have hle : stop n g i ≤ (i+1)*g := min_le_right _ _
  unfold start
  simp only [Nat.add_mul,Nat.one_mul] at hle
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
# A linear-time histogram procedure in the benchmark language

The input is an array of already computed residue indices in `[0,p)`.
The output is cleared and incremented once per input item. Multiplicities
are retained, including repeated equal residues.
-/

namespace ThreeSum.LightHistogram

open Light Finset

variable {lim : Limits} {P : Program} {d : ℕ}




@[simp] theorem count_zero (key : ℕ → ℕ) (r : ℕ) : count key r 0 = 0 := by
  simp [count]









































































































end ThreeSum.LightHistogram

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



































theorem modulus_pos (h J : ℕ) : 0 < modulus h J := pow_pos (localPrime_pos h) J

@[simp] theorem modulus_cast (h J : ℕ) : (modulus h J : ℤ) = globalModulus h J := by
  simp only [modulus,globalModulus,Nat.cast_pow]

section OriginalSources

variable {β : Type*} [DecidableEq β]



























end OriginalSources

end ThreeSum.BlockSourceEncoding

end

section


/-!
# Packed retained source banks indexed by occurrence vectors

Each bank retains its compact masks, coefficients, endpoints, flags, and
both complete source-stage families. Shared temporary transform workspace
follows all banks. Two header cells per occurrence contain the stage bases.
This layout lets the next actual source call preserve every earlier bank.
-/

namespace ThreeSum.LightBlockSourceBatchLayout

open SubsetAddress LightZetaStages

















theorem banks_le_slot (base count W cut i : ℕ) : banks base count ≤ slot base count W cut i :=
  Nat.le_add_right _ _


























theorem banks_le_work (base count W cut : ℕ) : banks base count ≤ work base count W cut := by
  have hm := banks_le_slot base count W cut count
  unfold work rowOut bitBase maskBase
  omega














theorem masks_le_work (base count W cut : ℕ) :
    maskBase base count W cut ≤ work base count W cut := by
  unfold work rowOut bitBase
  omega

































































end ThreeSum.LightBlockSourceBatchLayout

end

section


/-!
# Exact shared-bank dimensions and charge of the actual catalog

There are two stage families for each original band and occurrence vector.
The decoder and bank-loop overhead are included. Neither the number of
complete output subsets nor the three-valued query lift multiplies this
construction.
-/

namespace ThreeSum.BlockSourceCatalogCosts

open Scales TrimScales StageBounds CostLedger BlockSourceSharing SubsetAddress
open LightBlockSourceBatchLayout







theorem work_address (base count W cut : ℕ) :
    LightBlockSourceBatchLayout.work base count W cut =
      base+count*(stride W cut+2)+downsetCap W cut+W+2 := by
  unfold LightBlockSourceBatchLayout.work rowOut bitBase maskBase slot banks
  ring
























































































end ThreeSum.BlockSourceCatalogCosts

end

section


/-! # Packed original-band histograms and exact physical residue fibers -/

namespace ThreeSum.SourceBandLayout

open BandPartition LightHistogram SourceBuckets












theorem len_le_cap (n g i : ℕ) : len n g i ≤ cap n g := by
  have hn := stop_le n g i
  have hg := length_le n g i
  unfold len cap
  exact le_min (by omega) hg
























theorem hist_mono (base n g m : ℕ) : Monotone (hist base n g m) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _




theorem flat_end (base n g m i : ℕ) :
    flat base n g m i+cap n g = hist base n g m (i+1) := by
  unfold flat cursor offsets codes hist stride
  ring







theorem flat_end_le_work {base n g m i : ℕ} (hi : i < size n g) :
    flat base n g m i+cap n g ≤ work base n g m := by
  rw [flat_end]
  exact hist_mono base n g m (by omega)




















































end ThreeSum.SourceBandLayout

end

section


/-! # Retained original-band headers, histograms, and physical position fibers -/

namespace ThreeSum.SourceBandData

open Light BandPartition SourceBandLayout






































































theorem At.histogram_for_host {μ : ℕ → ℤ} {f : ℕ → ℤ} {base n g p m i : ℕ} {shift : ℤ}
    (H : At μ f base n g p m shift i) (r : ℕ) (hr : r < m) :
    μ (hist base n g m i+r) =
      (LightBlockSourceRetainedStages.histogram p m shift (fun j => f (start g i+j)) (len n g i) r : ℤ) :=
  H.histRead r hr
































end ThreeSum.SourceBandData

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


































































theorem Data.empty_histogram {μ : ℕ → ℤ} {fL fR v : ℕ → ℤ}
    {base NL NR g p m : ℕ} {shift d : ℤ}
    (H : Data μ fL fR base NL NR g p m shift) (r : ℕ) (hr : r < m) :
    μ (zeroBase base NL NR g m+r)=
      (LightBlockSourceRetainedStages.histogram p m d v 0 r : ℤ) := by
  simpa only [LightBlockSourceRetainedStages.histogram,LightHistogram.count_zero,Nat.cast_zero]
    using H.zero r hr.le

end ThreeSum.SourceBandPairData

end

section


/-! # Exact finite original-position sources for real and padded bands -/

namespace ThreeSum.SourceBandPartition

open BandPartition SourceBandLayout









































theorem len_eq_zero {n g i : ℕ} (hg : 0 < g) (hi : size n g ≤ i) : len n g i=0 := by
  by_cases hn : n=0
  · simp [len,stop,hn]
  · have hdiv : (n-1)/g < i := by
      simpa only [size,if_neg hn,Nat.add_one_le_iff] using hi
    have hmul : n-1 < i*g := (Nat.div_lt_iff_lt_mul hg).mp hdiv
    have hs := stop_le n g i
    unfold len start
    omega























end ThreeSum.SourceBandPartition

end

section


/-! # Padded histogram selection for independently chosen original bands -/

namespace ThreeSum.SourceBandPairSlices

open Light BandPartition SourceBandLayout SourceBandPairData












theorem histogram_end {base n g m zero i bound : ℕ}
    (hb : work base n g m ≤ bound) (hz : zero+m ≤ bound) :
    histogramPtr base n g m zero i+m ≤ bound := by
  unfold histogramPtr
  split_ifs with hi
  · have hh := flat_end_le_work (base := base) (m := m) hi
    unfold flat cursor offsets codes at hh
    omega
  · exact hz

theorem left_end (base NL NR g m i : ℕ) :
    histLeft base NL NR g m i+m ≤ next base NL NR g m := by
  have ho := ordered base NL NR g m
  exact histogram_end (by change rightBase base NL g m ≤ next base NL NR g m; omega)
    (by unfold next; omega)

theorem right_end (base NL NR g m i : ℕ) :
    histRight base NL NR g m i+m ≤ next base NL NR g m := by
  exact histogram_end (by change zeroBase base NL NR g m ≤ next base NL NR g m; unfold next; omega)
    (by unfold next; omega)

theorem left_histogram {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g p m i : ℕ} {shift : ℤ}
    (H : Data μ fL fR base NL NR g p m shift) (hg : 0 < g) (r : ℕ) (hr : r < m) :
    μ (histLeft base NL NR g m i+r)=
      (LightBlockSourceRetainedStages.histogram p m 0
        (fun j => fL (start g i+j)) (len NL g i) r : ℤ) := by
  by_cases hi : i < size NL g
  · simpa only [histLeft,histogramPtr,if_pos hi] using (H.left i hi).histogram_for_host r hr
  · rw [histLeft,histogramPtr,if_neg hi,SourceBandPartition.len_eq_zero hg (by omega)]
    exact H.empty_histogram r hr

theorem right_histogram {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g p m i : ℕ} {shift : ℤ}
    (H : Data μ fL fR base NL NR g p m shift) (hg : 0 < g) (r : ℕ) (hr : r < m) :
    μ (histRight base NL NR g m i+r)=
      (LightBlockSourceRetainedStages.histogram p m shift
        (fun j => fR (start g i+j)) (len NR g i) r : ℤ) := by
  by_cases hi : i < size NR g
  · simpa only [histRight,histogramPtr,if_pos hi] using (H.right i hi).histogram_for_host r hr
  · rw [histRight,histogramPtr,if_neg hi,SourceBandPartition.len_eq_zero hg (by omega)]
    exact H.empty_histogram r hr
















end ThreeSum.SourceBandPairSlices

end

section


/-! # Complete source banks per common band with preserved earlier banks -/

namespace ThreeSum.SourceBandBankLayout

open Light LightBlockSourceBatchLayout GlobalEncoding BlockSourceOccurrenceOrder




































theorem word_mono {NL NR NL' NR' h J : ℕ} (hl : NL ≤ NL') (hr : NR ≤ NR') :
    LightBlockSourceRetainedHost.word NL NR h J ≤ LightBlockSourceRetainedHost.word NL' NR' h J := by
  have hpl := Nat.mul_le_mul_left (2^(J*(512*h))) hl
  have hpr := Nat.mul_le_mul_left (2^(J*(512*h))) hr
  unfold LightBlockSourceRetainedHost.word LightSourceRetainedStages.word
  omega












































end ThreeSum.SourceBandBankLayout

end

section


/-! # Construct every occurrence bank for one common original-band index -/

namespace ThreeSum.LightSourceBandBankStep

open Light GlobalEncoding BlockEncoding BlockCoefficientRows BlockSourceEncoding
open LocalCoverBounds SubsetAddress LightBlockSourceBatchLayout BlockSourceOccurrenceOrder

set_option maxHeartbeats 3500000
set_option maxRecDepth 16000


























variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets_sourceProof {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {pair NL NR g p h J cut occ maps candidates histL histR base i : ℕ}
    {shift : ℤ} (H : SourceBandPairData.Stored μ fL fR pair NL NR g p (modulus h J) shift)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+12 ≤ lim.depth)
    (hg : 0 < g) (hi : i < SourceBandPairSlices.count NL NR g) (hcut : cut ≤ J*(512*h))
    (hpair : SourceBandPairData.next pair NL NR g (modulus h J) ≤ base)
    (hocc : occ+LightBlockSourceCatalog.count h J*J ≤ base)
    (hmaps : maps+2*(512*h)*scheduleSize h ≤ base)
    (hcandidates : candidates+scheduleSize h ≤ base)
    (hleft : histL+LightLocalCoverSchedule.rows h*localPrime h ≤ base)
    (hright : histR+LightLocalCoverSchedule.rows h*localPrime h ≤ base)
    (hspace : LightBlockSourceRetainedHost.space
      (work base (LightBlockSourceCatalog.count h J) (J*(512*h)) cut) h J ≤ lim.space)
    (hword : (word NL NR h J : ℤ) ≤ lim.word)
    (hoccRead : ∀ k < LightBlockSourceCatalog.count h J, ∀ j < J,
      μ (occ+k*J+j)=(occurrenceIndices (outputOccurrences (representative h J k)) j : ℤ))
    (hcover : BlockSourceCoverInput.Input μ h maps candidates histL histR) :
    Meets lim P pMain d
      [J,512*h,h,localPrime h,localBucketCap h,cut,modulus h J,occ,maps,candidates,histL,histR,
        pair,base,downsetCap (J*(512*h)) cut,LightBlockSourceCatalog.count h J,i]
      μ (time h J cut) (fun _ ν =>
        LightBlockSourceCatalog.Stored ν h J base cut (p : ℤ) shift
          (SourceBandPartition.source NL g i) (fun t : Fin NL => fL t.val)
          (SourceBandPartition.source NR g i) (fun t : Fin NR => fR t.val) ∧ Kept μ ν base) := by
  have hm := modulus_pos h J
  have hc : 0 < LightBlockSourceCatalog.count h J := pow_pos (OutputDecodeRecords.schedule_pos h) J
  have hs : work base (LightBlockSourceCatalog.count h J) (J*(512*h)) cut+(J*(512*h)+1) ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hwork : work base (LightBlockSourceCatalog.count h J) (J*(512*h)) cut ≤ lim.space := by omega
  have hbanks := banks_le_work base (LightBlockSourceCatalog.count h J) (J*(512*h)) cut
  have hbanksAddr : (base : ℤ)+2*(LightBlockSourceCatalog.count h J : ℤ) ≤ lim.word :=
    (by exact_mod_cast hbanks.trans hwork :
      (base : ℤ)+2*(LightBlockSourceCatalog.count h J : ℤ) ≤ lim.space).trans hw
  have hbase2 : base+2 ≤ lim.space := by unfold banks at hbanks; omega
  have hNL := BandPartition.size_le NL g
  have hNR := BandPartition.size_le NR g
  have hiN : i ≤ NL+NR := by unfold SourceBandPairSlices.count at hi; omega
  have hselWord : ((NL+NR+i+6 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word; omega)).trans hword
  have hsWord : (LightBlockSourceRetainedHost.word NL NR h J : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word; omega)).trans hword
  have h32 : (32 : ℤ) ≤ lim.word := by unfold word at hword; omega
  have hwidth : (J : ℤ)*(512*(h : ℤ)) ≤ lim.word :=
    (by exact_mod_cast (show J*(512*h) ≤ lim.space by omega) :
      (J : ℤ)*(512*(h : ℤ)) ≤ lim.space).trans hw
  have hwidthNonneg : (0 : ℤ) ≤ (J : ℤ)*(512*(h : ℤ)) := by positivity
  have hwidthPlus : (J*(512*h) : ℤ)+1 ≤ lim.word := by
    exact (by exact_mod_cast (show J*(512*h)+1 ≤ lim.space by omega) :
      (J*(512*h) : ℤ)+1 ≤ lim.space).trans hw
  have hstrideN : stride (J*(512*h)) cut ≤ lim.space := by
    have hp := Nat.le_mul_of_pos_left (stride (J*(512*h)) cut) hc
    rw [BlockSourceCatalogCosts.work_address] at hwork
    nlinarith
  have hstrideExpr : 5*downsetCap (J*(512*h)) cut+2*(J*(512*h))+2+
      2*(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ lim.space := by
    simpa only [stride,family,Nat.mul_assoc] using hstrideN
  have hstrideZ : (5 : ℤ)*(downsetCap (J*(512*h)) cut : ℤ)+2*(J*(512*h) : ℤ)+2+
      2*((J*(512*h) : ℤ)+1)*(downsetCap (J*(512*h)) cut : ℤ) ≤ lim.word :=
    (by exact_mod_cast hstrideExpr :
      (5 : ℤ)*(downsetCap (J*(512*h)) cut : ℤ)+2*(J*(512*h) : ℤ)+2+
        2*((J*(512*h) : ℤ)+1)*(downsetCap (J*(512*h)) cut : ℤ) ≤ lim.space).trans hw
  have hcapNonneg : (0 : ℤ) ≤ (downsetCap (J*(512*h)) cut : ℤ) := Int.natCast_nonneg _
  have hfamNonneg : (0 : ℤ) ≤ 2*((J*(512*h) : ℤ)+1)*(downsetCap (J*(512*h)) cut : ℤ) := by positivity
  have hfamilyNonneg : (0 : ℤ) ≤ ((J*(512*h) : ℤ)+1)*(downsetCap (J*(512*h)) cut : ℤ) := by positivity
  have hstrideAssoc : (5 : ℤ)*(downsetCap (J*(512*h)) cut : ℤ)+2*(J*(512*h) : ℤ)+2+
      2*(((J*(512*h) : ℤ)+1)*(downsetCap (J*(512*h)) cut : ℤ)) ≤ lim.word := by
    simpa only [mul_assoc] using hstrideZ
  have hmask := masks_le_work base (LightBlockSourceCatalog.count h J) (J*(512*h)) cut
  have hmaskAddr : (banks base (LightBlockSourceCatalog.count h J) : ℤ)+
      (LightBlockSourceCatalog.count h J : ℤ)*(stride (J*(512*h)) cut : ℤ) ≤ lim.word :=
    (by exact_mod_cast hmask.trans hwork :
      (banks base (LightBlockSourceCatalog.count h J) : ℤ)+
        (LightBlockSourceCatalog.count h J : ℤ)*(stride (J*(512*h)) cut : ℤ) ≤ lim.space).trans hw
  have hmaskProdNonneg : (0 : ℤ) ≤
      (LightBlockSourceCatalog.count h J : ℤ)*(stride (J*(512*h)) cut : ℤ) := by positivity
  have hbits : maskBase base (LightBlockSourceCatalog.count h J) (J*(512*h)) cut+
      downsetCap (J*(512*h)) cut ≤ lim.space := by unfold work rowOut bitBase at hwork; omega
  have hrow : bitBase base (LightBlockSourceCatalog.count h J) (J*(512*h)) cut+J*(512*h) ≤ lim.space := by
    unfold work rowOut at hwork
    omega
  have hrowZ : (bitBase base (LightBlockSourceCatalog.count h J) (J*(512*h)) cut : ℤ)+
      (J*(512*h) : ℤ) ≤ lim.word := (by exact_mod_cast hrow :
        (bitBase base (LightBlockSourceCatalog.count h J) (J*(512*h)) cut : ℤ)+(J*(512*h) : ℤ) ≤ lim.space).trans hw
  have hworkN : rowOut base (LightBlockSourceCatalog.count h J) (J*(512*h)) cut+2 ≤ lim.space := hwork
  have hsrcL := (SourceBandPairSlices.left_end pair NL NR g (modulus h J) i).trans hpair
  have hsrcR := (SourceBandPairSlices.right_end pair NL NR g (modulus h J) i).trans hpair
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
    (first
      |
        refine
          Light.Ends.callToThen
            ((LightSourceBandHistSelect.meets (d := d + 1) C.select H hw hm hpair
                hbase2 hselWord)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (LightSourceBandHistSelect.meets (d := d + 1) C.select H hw hm hpair
              hbase2 hselWord)
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
        ((rintro unused ν ⟨headL, headR, kept⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (J * (512 * h) : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (stride (J * (512 * h)) cut : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, stride,
                family, mul_assoc]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [stride, family, mul_assoc] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, stride, family,
                mul_assoc] <;>
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
        Light.Ends.setToThen (banks base (LightBlockSourceCatalog.count h J) : ℕ)
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, banks]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [banks] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, banks] <;> omega)));
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
        Light.Ends.setToThen
          (maskBase base (LightBlockSourceCatalog.count h J) (J * (512 * h)) cut :
            ℕ)
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                maskBase, slot]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [maskBase, slot] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, maskBase, slot] <;>
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
        Light.Ends.setToThen
          (bitBase base (LightBlockSourceCatalog.count h J) (J * (512 * h)) cut :
            ℕ)
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                bitBase]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [bitBase] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, bitBase] <;> omega)));
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
        Light.Ends.setToThen
          (rowOut base (LightBlockSourceCatalog.count h J) (J * (512 * h)) cut :
            ℕ)
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                rowOut]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [rowOut] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, rowOut] <;> omega)));
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
        Light.Ends.setToThen
          (work base (LightBlockSourceCatalog.count h J) (J * (512 * h)) cut : ℕ)
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, work]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [work] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, work] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  have H' := H.of_kept hm kept hpair
  have hcover' := hcover.of_kept kept hmaps hcandidates hleft hright
  have hrows : ∀ k < LightBlockSourceCatalog.count h J, ∀ j < J,
      ν (occ+k*J+j)=(occurrenceIndices (outputOccurrences (representative h J k)) j : ℤ) := by
    intro k hk j hj
    have hp := Nat.mul_le_mul_right J (show k+1 ≤ LightBlockSourceCatalog.count h J by omega)
    exact (kept _ (by nlinarith)).trans (hoccRead k hk j hj)
  have hlenL := (SourceBandLayout.len_le_cap NL g i).trans (min_le_left _ _)
  have hlenR := (SourceBandLayout.len_le_cap NR g i).trans (min_le_left _ _)
  have hword' := (Int.ofNat_le.mpr (SourceBandBankLayout.word_mono (h := h) (J := J) hlenL hlenR)).trans hsWord
  have hrun := C.batch.meets (d := d+1) (μ := ν) (cut := cut) (p := p) (shift := shift)
    (occ := occ) (maps := maps) (candidates := candidates) (histL := histL) (histR := histR)
    (sourceHistL := SourceBandPairSlices.histLeft pair NL NR g (modulus h J) i)
    (sourceHistR := SourceBandPairSlices.histRight pair NL NR g (modulus h J) i)
    (base := base) (count := LightBlockSourceCatalog.count h J)
    (SourceBandPartition.source NL g i) (fun t : Fin NL => fL t.val)
    (SourceBandPartition.source NR g i) (fun t : Fin NR => fR t.val) (representative h J)
    (fun j => fL (BandPartition.start g i+j)) (fun j => fR (BandPartition.start g i+j))
    (SourceBandPartition.equiv NL g i) (SourceBandPartition.equiv NR g i)
    hw (by omega) hcut hocc hmaps hcandidates hleft hright hsrcL hsrcR hspace hword'
    (fun _ => rfl) (fun _ => rfl)
    (SourceBandPairSlices.left_histogram H'.toData hg)
    (SourceBandPairSlices.right_histogram H'.toData hg) hrows hcover'
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
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, headL,
                headR]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [headL, headR] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, headL, headR] <;> omega)));
    (on_goal -1 =>
        ((rintro result ν' ⟨stored, kept'⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  exact ⟨stored,fun a ha => (kept' a ha).trans (kept a ha)⟩

end ThreeSum.LightSourceBandBankStep

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (C : ThreeSum.LightSourceBandBankStep.Procs P pMain)
  {μ fL fR : Nat → Int} {pair NL NR g p h J cut occ maps candidates histL histR base i : Nat} {shift : Int},
  ThreeSum.SourceBandPairData.Stored μ fL fR pair NL NR g p (ThreeSum.BlockSourceEncoding.modulus h J) shift →
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
      @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
            (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
          lim.depth →
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) g →
          @LT.lt.{0} Nat instLTNat i (ThreeSum.SourceBandPairSlices.count NL NR g) →
            @LE.le.{0} Nat instLENat cut
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)) →
              @LE.le.{0} Nat instLENat
                  (ThreeSum.SourceBandPairData.next pair NL NR g (ThreeSum.BlockSourceEncoding.modulus h J)) base →
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
                      base →
                    @LE.le.{0} Nat instLENat
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) candidates
                          (ThreeSum.GlobalEncoding.scheduleSize h))
                        base →
                      @LE.le.{0} Nat instLENat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histL
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (ThreeSum.LightLocalCoverSchedule.rows h) (ThreeSum.LocalCoverBounds.localPrime h)))
                          base →
                        @LE.le.{0} Nat instLENat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histR
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (ThreeSum.LightLocalCoverSchedule.rows h) (ThreeSum.LocalCoverBounds.localPrime h)))
                            base →
                          @LE.le.{0} Nat instLENat
                              (ThreeSum.LightBlockSourceRetainedHost.space
                                (ThreeSum.LightBlockSourceBatchLayout.work base
                                  (ThreeSum.LightBlockSourceCatalog.count h J)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                                  cut)
                                h J)
                              lim.space →
                            @LE.le.{0} Int Int.instLEInt
                                (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightSourceBandBankStep.word NL NR h J))
                                lim.word →
                              (∀ (k : Nat),
                                  @LT.lt.{0} Nat instLTNat k (ThreeSum.LightBlockSourceCatalog.count h J) →
                                    ∀ (j : Nat),
                                      @LT.lt.{0} Nat instLTNat j J →
                                        @Eq.{1} Int
                                          (μ
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) occ
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) k J))
                                              j))
                                          (@Nat.cast.{0} Int instNatCastInt
                                            (@ThreeSum.BlockCoefficientRows.occurrenceIndices h J
                                              (@ThreeSum.BlockEncoding.outputOccurrences h J
                                                (ThreeSum.BlockSourceOccurrenceOrder.representative h J k))
                                              j))) →
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
                                                              (@List.cons.{0} Int
                                                                (@Nat.cast.{0} Int instNatCastInt base)
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
                                                                      (@Nat.cast.{0} Int instNatCastInt i)
                                                                      (@List.nil.{0} Int))))))))))))))))))
                                    μ (ThreeSum.LightSourceBandBankStep.time h J cut) fun (x : Int) (ν : Nat → Int) =>
                                    And
                                      (@ThreeSum.LightBlockSourceCatalog.Stored.{0, 0} (Fin NL) (Fin NR)
                                        (Fin.fintype NL) (Fin.fintype NR) (instDecidableEqFin NL)
                                        (instDecidableEqFin NR) ν h J base cut (@Nat.cast.{0} Int instNatCastInt p)
                                        shift (ThreeSum.SourceBandPartition.source NL g i)
                                        (fun (t : Fin NL) => fL (@Fin.val NL t))
                                        (ThreeSum.SourceBandPartition.source NR g i) fun (t : Fin NR) =>
                                        fR (@Fin.val NR t))
                                      (Light.Kept μ ν base) := by
  exact @ThreeSum.LightSourceBandBankStep.Procs.meets_sourceProof

#print axioms solution
