-- Prove2me | solution 1 for ThreeSum.LightBlockSourceRetainedHost.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:52:05.420851+00:00
-- url     : https://prove2.me/submissions/a9d7cb85-912d-4f5f-ad5d-9a804006a3da

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
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
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
import Mathlib.Data.List.Range
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
import Mathlib.Tactic
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
import Theorems.Thm_ThreeSum_BlockSourceCoverInput_Input_of_kept
import Theorems.Thm_ThreeSum_LightBlockSourcePreparation_meets
import Theorems.Thm_ThreeSum_LightBlockSourceRetainedStages_meets_left
import Theorems.Thm_ThreeSum_LightBlockSourceRetainedStages_meets_right
import Theorems.Thm_ThreeSum_LightDownsetEnumerationSetup_meets
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt


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
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.BlockSourceFlags
end ThreeSum.BlockSourceFlags
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockSourceBuild
end ThreeSum.LightBlockSourceBuild
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSumApsp
end ThreeSumApsp

section


/-!
# Compact addresses for bounded-cardinality bit masks

Both ranking and enumeration recurse on the highest available bit. The
enumerator stops immediately when the requested layer is empty. In
particular, it does not enumerate the ambient Boolean cube and filter it.
-/

namespace ThreeSum.SubsetAddress

set_option maxRecDepth 4000

open Finset
open scoped BigOperators






































































































































































































































@[simp] theorem layerOffset_zero (L : ℕ) : layerOffset L 0 = 0 := by
  simp [layerOffset]

theorem layerOffset_succ (L k : ℕ) :
    layerOffset L (k + 1) = layerOffset L k + L.choose k := by
  exact Finset.sum_range_succ _ _

theorem layerOffset_mono (L : ℕ) : Monotone (layerOffset L) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [layerOffset_succ]
  omega






theorem downsetRank_lt {L cut m : ℕ} (hm : m < 2 ^ L) (hk : weight L m ≤ cut) :
    downsetRank L m < downsetCap L cut := by
  have hmask : IsMask L (weight L m) m := ⟨hm, rfl⟩
  have hr := layerRank_lt hmask
  unfold downsetRank downsetCap
  calc
    _ < layerOffset L (weight L m) + L.choose (weight L m) := Nat.add_lt_add_left hr _
    _ = layerOffset L (weight L m + 1) := (layerOffset_succ L _).symm
    _ ≤ _ := layerOffset_mono L (Nat.succ_le_succ (le_min hk hmask.le_width))






























theorem enumerateThrough_length (L k : ℕ) :
    (enumerateThrough L k).length = layerOffset L (k + 1) := by
  induction k with
  | zero => simp [enumerateThrough, enumerateLayer_length, layerOffset_succ]
  | succ k ih =>
      rw [enumerateThrough, List.length_append, ih, enumerateLayer_length,
        layerOffset_succ L (k + 1)]

theorem enumerateDownset_length (L cut : ℕ) :
    (enumerateDownset L cut).length = downsetCap L cut :=
  enumerateThrough_length L (min cut L)

theorem mem_enumerateThrough (L k m : ℕ) :
    m ∈ enumerateThrough L k ↔ m < 2 ^ L ∧ weight L m ≤ k := by
  induction k with
  | zero => simp [enumerateThrough, mem_enumerateLayer, IsMask]
  | succ k ih =>
      simp only [enumerateThrough, List.mem_append, ih, mem_enumerateLayer, IsMask]
      omega

theorem mem_enumerateDownset (L cut m : ℕ) :
    m ∈ enumerateDownset L cut ↔ m < 2 ^ L ∧ weight L m ≤ cut := by
  rw [enumerateDownset, mem_enumerateThrough]
  constructor
  · rintro ⟨hm, hk⟩
    exact ⟨hm, hk.trans (min_le_left _ _)⟩
  · rintro ⟨hm, hk⟩
    exact ⟨hm, le_min hk (weight_le_width hm)⟩































































































theorem subsetRank_lt {L cut : ℕ} {s : Finset (Fin L)} (hs : s.card ≤ cut) :
    subsetRank s < downsetCap L cut := by
  have hm := subsetMask_isMask s
  exact downsetRank_lt hm.1 (hm.2.trans_le hs)







































end ThreeSum.SubsetAddress

end

section


/-!
# Explicit row-major encoding of the block ground set

Block coordinates are numbered by `block * width + coordinate`. The
equivalence connects compact machine-mask tables on `Fin (J*L)` with the
sigma-typed block sets in the reporting proof. Flattened one-hot coefficients
already include their positional radix factors.
-/

namespace ThreeSum.BlockIndex

open Finset BlockRows BlockEncoding GlobalEncoding LocalHashMoments LocalCoverBounds
open scoped BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false


























@[simp] theorem index_unindex {J L : ℕ} (S : Finset (Fin (J*L))) :
    indexSet (unindexSet (J := J) (L := L) S) = S := by
  ext c
  simp [unindexSet,indexSet]
























































































end ThreeSum.BlockIndex

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
































































































































/-- Reading a cell of a segment of natural numbers, with the proof that the index is in range. -/
theorem SegN.getElem {l : List ℕ} (h : SegN μ a l) {i : ℕ} (hi : i < l.length) :
    μ (a + i) = (l[i] : ℕ) := by
  rw [h i (by simpa using hi), List.getElem_map]































































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


/-!
# The actual compact enumeration uses the actual compact table addresses

This bridges a sequentially constructed source array to `TableAt`: the mask
stored at `subsetRank S` by the existing enumerator is exactly `subsetMask S`.
No additional scatter, rank oracle, or arbitrary enumeration is required.
-/

namespace ThreeSum.SourceTableLayout

open SubsetAddress

set_option maxHeartbeats 800000





























































































theorem maskAt_mem {L cut i : ℕ} (hi : i < downsetCap L cut) :
    maskAt L cut i ∈ enumerateDownset L cut := by
  unfold maskAt
  rw [List.getD_eq_getElem _ _ (by simpa only [enumerateDownset_length] using hi)]
  exact List.getElem_mem _

theorem maskAt_lt {L cut i : ℕ} (hi : i < downsetCap L cut) :
    maskAt L cut i < 2^L :=
  ((mem_enumerateDownset L cut _).mp (maskAt_mem hi)).1






theorem subsetMask_setAt {L cut i : ℕ} (hi : i < downsetCap L cut) :
    subsetMask (setAt L cut i) = maskAt L cut i :=
  MaskDecode.subsetMask_decode (maskAt_lt hi)
























end ThreeSum.SourceTableLayout

end

section


/-! # Compact source arrays in the unchanged block-query coordinate system -/

namespace ThreeSum.BlockSourceTableLayout

open SubsetAddress BlockIndex BlockEncoding BlockRows GlobalEncoding




theorem mask_sets {h J cut i : ℕ} (hi : i < downsetCap (J*(512*h)) cut) :
    subsetMask (indexSet (sets h J cut i)) = SourceTableLayout.maskAt (J*(512*h)) cut i := by
  rw [sets,index_unindex,SourceTableLayout.subsetMask_setAt hi]
























end ThreeSum.BlockSourceTableLayout

end

section


/-!
# Per-occurrence source construction with shared band histograms

For a fixed band pair, modulus, and common offset, this host constructs its
own compact masks, coefficient rows, endpoint arrays, and independent flags.
It then gathers from the retained band histograms and constructs both exact
original suffix-stage families. Histogram scans belong outside this loop.
-/

namespace ThreeSum.LightBlockSourceRetainedHost

open Light BlockEncoding GlobalEncoding BlockIndex BlockCoefficientRows
open SubsetAddress LightSubsetAddress LightPascal LocalCoverBounds BlockSourceFlags
open BlockSourceEncoding LightBlockSourceBuild

set_option maxHeartbeats 4000000
set_option maxRecDepth 14000









































variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets_sourceProof {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {h J cut p NL NR occ maps candidates histL histR sourceHistL sourceHistR
      masks coeff0 coeff1 rawLeft rawRight flags baseL baseR maskBase bitBase rowOut work : ℕ}
    {shift : ℤ} (B : Finset β) (b : β → ℤ) (A : Finset γ) (a : γ → ℤ)
    (q : GlobalOutput h J) (vL vR : ℕ → ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ A)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+9 ≤ lim.depth)
    (hcut : cut ≤ J*(512*h))
    (hocc : occ+J ≤ masks) (hmaps : maps+2*(512*h)*scheduleSize h ≤ masks)
    (hcandidates : candidates+scheduleSize h ≤ masks)
    (hleft : histL+LightLocalCoverSchedule.rows h*localPrime h ≤ masks)
    (hright : histR+LightLocalCoverSchedule.rows h*localPrime h ≤ masks)
    (hsourceHistL : sourceHistL+modulus h J ≤ masks)
    (hsourceHistR : sourceHistR+modulus h J ≤ masks)
    (hmasks : masks+downsetCap (J*(512*h)) cut ≤ coeff0)
    (hc0 : coeff0+J*(512*h) ≤ coeff1) (hc1 : coeff1+J*(512*h) ≤ rawLeft)
    (hrawLeft : rawLeft+downsetCap (J*(512*h)) cut ≤ rawRight)
    (hrawRight : rawRight+downsetCap (J*(512*h)) cut ≤ flags)
    (hflags : flags+2*downsetCap (J*(512*h)) cut+2 ≤ baseL)
    (hbaseL : baseL+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ baseR)
    (hbaseR : baseR+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ maskBase)
    (hmaskBase : maskBase+downsetCap (J*(512*h)) cut ≤ bitBase)
    (hbits : bitBase+J*(512*h) ≤ rowOut) (hrowOut : rowOut+2 ≤ work)
    (hspace : space work h J ≤ lim.space)
    (hword : (word NL NR h J : ℤ) ≤ lim.word)
    (hinputL : ∀ i : Fin NL, vL i.val = b (eL i))
    (hinputR : ∀ i : Fin NR, vR i.val = a (eR i))
    (hhistReadL : ∀ r < modulus h J,
      μ (sourceHistL+r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) 0 vL NL r : ℤ))
    (hhistReadR : ∀ r < modulus h J,
      μ (sourceHistR+r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) shift vR NR r : ℤ))
    (hoccRead : ∀ j < J, μ (occ+j) = (occurrenceIndices (outputOccurrences q) j : ℤ))
    (hcover : BlockSourceCoverInput.Input μ h maps candidates histL histR) :
    Meets lim P pMain d
      [J,512*h,h,localPrime h,localBucketCap h,cut,modulus h J,occ,maps,candidates,
        histL,histR,sourceHistL,sourceHistR,masks,coeff0,coeff1,rawLeft,rawRight,flags,
        baseL,baseR,maskBase,bitBase,rowOut,work]
      μ (time h J cut) (fun _ ν =>
        LightZetaStages.StoredThrough ν baseL cut (BlockIndexedQuery.leftSource (p : ℤ) B b q) (J*(512*h)) ∧
        LightZetaStages.StoredThrough ν baseR cut (BlockIndexedQuery.rightSource (p : ℤ) shift A a q) (J*(512*h)) ∧
        Kept μ ν masks) := by
  have hsEnum : work+(J*(512*h)+1) ≤ lim.space := (le_max_left _ _).trans hspace
  have hsRest := (le_max_right _ _).trans hspace
  have hsPrep : LightSourcePreparation.space work J (512*h) (localPrime h) ≤ lim.space :=
    (le_max_left _ _).trans hsRest
  have hsStages : LightSourceRetainedStages.space work (J*(512*h)) (endpointBound h J) ≤ lim.space :=
    (le_max_right _ _).trans hsRest
  have hwEnum : ((2^(J*(512*h)+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : 2^(J*(512*h)+1) ≤ word NL NR h J :=
      (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwPrep : (LightSourcePreparation.word J (512*h) (localPrime h) (localPrime h)
      ((512*h).choose h) (localBucketCap h) : ℤ) ≤ lim.word := by
    have hh : LightSourcePreparation.word J (512*h) (localPrime h) (localPrime h)
        ((512*h).choose h) (localBucketCap h) ≤ word NL NR h J :=
      (Nat.le_add_left _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwLeft : (LightSourceRetainedStages.word (J*(512*h)) (modulus h J) (endpointBound h J) NL : ℤ) ≤ lim.word := by
    have hh : LightSourceRetainedStages.word (J*(512*h)) (modulus h J) (endpointBound h J) NL ≤
        word NL NR h J := (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwRight : (LightSourceRetainedStages.word (J*(512*h)) (modulus h J) (endpointBound h J) NR : ℤ) ≤ lim.word := by
    have hh : LightSourceRetainedStages.word (J*(512*h)) (modulus h J) (endpointBound h J) NR ≤
        word NL NR h J := Nat.le_add_left _ _
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwidth : (J : ℤ)*(512*(h : ℤ)) ≤ lim.word := by
    exact (by exact_mod_cast (show J*(512*h) ≤ lim.space by omega) :
      (J : ℤ)*(512*(h : ℤ)) ≤ lim.space).trans hw
  have hwidthNonneg : (0 : ℤ) ≤ (J : ℤ)*(512*(h : ℤ)) := by positivity
  apply Meets.of_body C.main
  unfold body time
  have he := LightDownsetEnumerationSetup.meets (d := d+1) (μ := μ) (L := J*(512*h))
    (cut := cut) (dst := masks) (work := work) C.enumMain C.powers C.downset C.layer
    hw hsEnum hwEnum hcut (by omega) (by omega)
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
                LightDownsetEnumerationSetup.time, LightDownsetEnumeration.time,
                LightSourcePreparation.time, LightSourceRetainedStages.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightDownsetEnumerationSetup.time, LightDownsetEnumeration.time,
                LightSourcePreparation.time, LightSourceRetainedStages.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul,
                LightDownsetEnumerationSetup.time, LightDownsetEnumeration.time,
                LightSourcePreparation.time, LightSourceRetainedStages.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro count ν₁ ⟨hcount, hseg, _, kept₁⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  subst count
  have keptEnum : Kept μ ν₁ masks := by
    intro x hx
    exact kept₁ x ⟨by omega,Or.inl hx⟩
  have hcover' := hcover.of_kept keptEnum hmaps hcandidates hleft hright
  have hocc' : ∀ j < J, ν₁ (occ+j) = (occurrenceIndices (outputOccurrences q) j : ℤ) := by
    intro j hj
    exact (keptEnum _ (by omega)).trans (hoccRead j hj)
  have hmaskRead : ∀ i < downsetCap (J*(512*h)) cut,
      ν₁ (masks+i) = (subsetMask (indexSet (BlockSourceTableLayout.sets h J cut i)) : ℤ) := by
    intro i hi
    rw [BlockSourceTableLayout.mask_sets hi,SourceTableLayout.maskAt,
      List.getD_eq_getElem _ _ (by simpa only [enumerateDownset_length] using hi)]
    exact hseg.getElem (by simpa only [enumerateDownset_length] using hi)
  have hpRun := LightBlockSourcePreparation.meets (d := d+1) (μ := ν₁) C.prepare
    (occ := occ) (maps := maps) (candidates := candidates) (histL := histL) (histR := histR)
    (masks := masks) (n := downsetCap (J*(512*h)) cut) (coeff0 := coeff0) (coeff1 := coeff1)
    (rawLeft := rawLeft) (rawRight := rawRight) (flags := flags) (bitBase := bitBase)
    (rowOut := rowOut) (work := work) (outputOccurrences q) (BlockSourceTableLayout.sets h J cut)
    hw (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hmasks hc0 hc1
    hrawLeft hrawRight (by omega) hbits hrowOut hsPrep hwPrep hocc'
    hcover'.candidates hcover'.leftRows hcover'.rightRows hcover'.leftCounts hcover'.rightCounts hmaskRead
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
      | refine Light.Ends.callToThen (hpRun _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hpRun ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightDownsetEnumerationSetup.time, LightDownsetEnumeration.time,
                LightSourcePreparation.time, LightSourceRetainedStages.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightDownsetEnumerationSetup.time, LightDownsetEnumeration.time,
                LightSourcePreparation.time, LightSourceRetainedStages.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul,
                LightDownsetEnumerationSetup.time, LightDownsetEnumeration.time,
                LightSourcePreparation.time, LightSourceRetainedStages.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro r ν₂ ⟨rawL, rawR, flagL, flagR, kept₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have keptPrep : Kept μ ν₂ masks := by
    intro x hx
    exact (kept₂ x (by omega)).trans (keptEnum x hx)
  have hhL : ∀ r < modulus h J,
      ν₂ (sourceHistL+r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) 0 vL NL r : ℤ) := by
    intro r hr
    exact (keptPrep _ (by omega)).trans (hhistReadL r hr)
  have hlRun := LightBlockSourceRetainedStages.meets_left (d := d+1) (μ := ν₂) C.stages
    (N := NL) (raw := rawLeft) (flags := flags) (p := p) (table := sourceHistL)
    (base := baseL) (work := work) (cut := cut) (maskBase := maskBase)
    B b q vL eL hw (by omega) hcut (by omega) (by omega) (by omega) (by omega)
    (by omega) hsStages hwLeft hinputL hhL rawL flagL
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
      | refine Light.Ends.callToThen (hlRun _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hlRun ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightDownsetEnumerationSetup.time, LightDownsetEnumeration.time,
                LightSourcePreparation.time, LightSourceRetainedStages.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightDownsetEnumerationSetup.time, LightDownsetEnumeration.time,
                LightSourcePreparation.time, LightSourceRetainedStages.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul,
                LightDownsetEnumerationSetup.time, LightDownsetEnumeration.time,
                LightSourcePreparation.time, LightSourceRetainedStages.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro r ν₃ ⟨storedL, kept₃⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have keptLeft : Kept μ ν₃ masks := by
    intro x hx
    exact (kept₃ x (by omega)).trans (keptPrep x hx)
  have hhR : ∀ r < modulus h J,
      ν₃ (sourceHistR+r) = (LightBlockSourceRetainedStages.histogram p (modulus h J) shift vR NR r : ℤ) := by
    intro r hr
    exact (keptLeft _ (by omega)).trans (hhistReadR r hr)
  have rawR' : ∀ i < downsetCap (J*(512*h)) cut,
      ν₃ (rawRight+i) = endpointRight (outputOccurrences q) (BlockSourceTableLayout.sets h J cut i) := by
    intro i hi
    exact (kept₃ _ (by omega)).trans (rawR i hi)
  have flagR' : ∀ i < downsetCap (J*(512*h)) cut,
      ν₃ (flags+downsetCap (J*(512*h)) cut+i) =
        (if RightAllowed (outputOccurrences q) (BlockSourceTableLayout.sets h J cut i) then 1 else 0 : ℕ) := by
    intro i hi
    exact (kept₃ _ (by omega)).trans (flagR i hi)
  have hrRun := LightBlockSourceRetainedStages.meets_right (d := d+1) (μ := ν₃) C.stages
    (N := NR) (raw := rawRight) (flags := flags+downsetCap (J*(512*h)) cut) (p := p)
    (table := sourceHistR) (base := baseR) (work := work) (cut := cut) (maskBase := maskBase)
    A a q vR eR hw (by omega) hcut (by omega) (by omega) (by omega) hbaseR
    (by omega) hsStages hwRight hinputR hhR rawR' flagR'
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
      | refine Light.Ends.callToThen (hrRun _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hrRun ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightDownsetEnumerationSetup.time, LightDownsetEnumeration.time,
                LightSourcePreparation.time, LightSourceRetainedStages.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightDownsetEnumerationSetup.time, LightDownsetEnumeration.time,
                LightSourcePreparation.time, LightSourceRetainedStages.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul,
                LightDownsetEnumerationSetup.time, LightDownsetEnumeration.time,
                LightSourcePreparation.time, LightSourceRetainedStages.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro r ν₄ ⟨storedR, kept₄⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  refine ⟨?_,storedR,?_⟩
  · intro j hj S hS
    have hr := subsetRank_lt hS
    have hmul := Nat.mul_le_mul_right (downsetCap (J*(512*h)) cut) (Nat.succ_le_succ hj)
    have haddr : LightZetaStages.stageBase baseL (downsetCap (J*(512*h)) cut) j+subsetRank S < baseR := by
      calc
        LightZetaStages.stageBase baseL (downsetCap (J*(512*h)) cut) j+subsetRank S
            < baseL+j*downsetCap (J*(512*h)) cut+downsetCap (J*(512*h)) cut :=
          Nat.add_lt_add_left hr _
        _ = baseL+(j+1)*downsetCap (J*(512*h)) cut := by ring
        _ ≤ baseL+(J*(512*h)+1)*downsetCap (J*(512*h)) cut := Nat.add_le_add_left hmul _
        _ ≤ baseR := hbaseL
    exact (kept₄ _ haddr).trans (storedL j hj S hS)
  · intro x hx
    exact (kept₄ x (by omega)).trans (keptLeft x hx)

end ThreeSum.LightBlockSourceRetainedHost

end

universe u_1 u_2

theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d : Nat} {β : Type u_1} {γ : Type u_2} [Fintype.{u_1} β] [Fintype.{u_2} γ]
  [DecidableEq.{u_1 + 1} β] [DecidableEq.{u_2 + 1} γ] {pMain : Nat}
  (C : ThreeSum.LightBlockSourceRetainedHost.Procs P pMain) {μ : Nat → Int}
  {h J cut p NL NR occ maps candidates histL histR sourceHistL sourceHistR masks coeff0 coeff1 rawLeft rawRight flags
    baseL baseR maskBase bitBase rowOut work : Nat}
  {shift : Int} (B : Finset.{u_1} β) (b : β → Int) (A : Finset.{u_2} γ) (a : γ → Int)
  (q : ThreeSum.GlobalEncoding.GlobalOutput h J) (vL vR : Nat → Int) (eL : Equiv.{1, u_1 + 1} (Fin NL) ↥B)
  (eR : Equiv.{1, u_2 + 1} (Fin NR) ↥A)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
        (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
      lim.depth)
  (hcut :
    @LE.le.{0} Nat instLENat cut
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
  (hocc : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) occ J) masks)
  (hmaps :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
          (ThreeSum.GlobalEncoding.scheduleSize h)))
      masks)
  (hcandidates :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) candidates
        (ThreeSum.GlobalEncoding.scheduleSize h))
      masks)
  (hleft :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histL
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.LightLocalCoverSchedule.rows h)
          (ThreeSum.LocalCoverBounds.localPrime h)))
      masks)
  (hright :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histR
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.LightLocalCoverSchedule.rows h)
          (ThreeSum.LocalCoverBounds.localPrime h)))
      masks)
  (hsourceHistL :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) sourceHistL
        (ThreeSum.BlockSourceEncoding.modulus h J))
      masks)
  (hsourceHistR :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) sourceHistR
        (ThreeSum.BlockSourceEncoding.modulus h J))
      masks)
  (hmasks :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) masks
        (ThreeSum.SubsetAddress.downsetCap
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
          cut))
      coeff0)
  (hc0 :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) coeff0
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
      coeff1)
  (hc1 :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) coeff1
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
      rawLeft)
  (hrawLeft :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rawLeft
        (ThreeSum.SubsetAddress.downsetCap
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
          cut))
      rawRight)
  (hrawRight :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rawRight
        (ThreeSum.SubsetAddress.downsetCap
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
          cut))
      flags)
  (hflags :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flags
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (ThreeSum.SubsetAddress.downsetCap
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
              cut)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      baseL)
  (hbaseL :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) baseL
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (ThreeSum.SubsetAddress.downsetCap
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
            cut)))
      baseR)
  (hbaseR :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) baseR
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (ThreeSum.SubsetAddress.downsetCap
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
            cut)))
      maskBase)
  (hmaskBase :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maskBase
        (ThreeSum.SubsetAddress.downsetCap
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
          cut))
      bitBase)
  (hbits :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bitBase
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
      rowOut)
  (hrowOut :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rowOut
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      work)
  (hspace : @LE.le.{0} Nat instLENat (ThreeSum.LightBlockSourceRetainedHost.space work h J) lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightBlockSourceRetainedHost.word NL NR h J)) lim.word)
  (hinputL :
    ∀ (i : Fin NL),
      @Eq.{1} Int (vL (@Fin.val NL i))
        (b
          (@Subtype.val.{u_1 + 1} β
            (fun (x : β) =>
              @Membership.mem.{u_1, u_1} β (Finset.{u_1} β)
                (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} β) β (@Finset.instSetLike.{u_1} β)) B x)
            (@DFunLike.coe.{u_1 + 1, 1, u_1 + 1} (Equiv.{1, u_1 + 1} (Fin NL) ↥B) (Fin NL) (fun (x : Fin NL) => ↥B)
              (@EquivLike.toFunLike.{u_1 + 1, 1, u_1 + 1} (Equiv.{1, u_1 + 1} (Fin NL) ↥B) (Fin NL) (↥B)
                (@Equiv.instEquivLike.{1, u_1 + 1} (Fin NL) ↥B))
              eL i))))
  (hinputR :
    ∀ (i : Fin NR),
      @Eq.{1} Int (vR (@Fin.val NR i))
        (a
          (@Subtype.val.{u_2 + 1} γ
            (fun (x : γ) =>
              @Membership.mem.{u_2, u_2} γ (Finset.{u_2} γ)
                (@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} γ) γ (@Finset.instSetLike.{u_2} γ)) A x)
            (@DFunLike.coe.{u_2 + 1, 1, u_2 + 1} (Equiv.{1, u_2 + 1} (Fin NR) ↥A) (Fin NR) (fun (x : Fin NR) => ↥A)
              (@EquivLike.toFunLike.{u_2 + 1, 1, u_2 + 1} (Equiv.{1, u_2 + 1} (Fin NR) ↥A) (Fin NR) (↥A)
                (@Equiv.instEquivLike.{1, u_2 + 1} (Fin NR) ↥A))
              eR i))))
  (hhistReadL :
    ∀ (r : Nat),
      @LT.lt.{0} Nat instLTNat r (ThreeSum.BlockSourceEncoding.modulus h J) →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) sourceHistL r))
          (@Nat.cast.{0} Int instNatCastInt
            (ThreeSum.LightBlockSourceRetainedStages.histogram p (ThreeSum.BlockSourceEncoding.modulus h J)
              (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) vL NL r)))
  (hhistReadR :
    ∀ (r : Nat),
      @LT.lt.{0} Nat instLTNat r (ThreeSum.BlockSourceEncoding.modulus h J) →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) sourceHistR r))
          (@Nat.cast.{0} Int instNatCastInt
            (ThreeSum.LightBlockSourceRetainedStages.histogram p (ThreeSum.BlockSourceEncoding.modulus h J) shift vR NR
              r)))
  (hoccRead :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j J →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) occ j))
          (@Nat.cast.{0} Int instNatCastInt
            (@ThreeSum.BlockCoefficientRows.occurrenceIndices h J (@ThreeSum.BlockEncoding.outputOccurrences h J q) j)))
  (hcover : ThreeSum.BlockSourceCoverInput.Input μ h maps candidates histL histR),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt J)
      (@List.cons.{0} Int
        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
          (@OfNat.ofNat.{0} Int (nat_lit 512) (@instOfNat (nat_lit 512))) (@Nat.cast.{0} Int instNatCastInt h))
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt h)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LocalCoverBounds.localPrime h))
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LocalCoverBounds.localBucketCap h))
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cut)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.BlockSourceEncoding.modulus h J))
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt occ)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt maps)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt candidates)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt histL)
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt histR)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt sourceHistL)
                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt sourceHistR)
                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt masks)
                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt coeff0)
                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt coeff1)
                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rawLeft)
                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rawRight)
                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt flags)
                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt baseL)
                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt baseR)
                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt maskBase)
                                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt bitBase)
                                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rowOut)
                                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                                        (@List.nil.{0} Int)))))))))))))))))))))))))))
    μ (ThreeSum.LightBlockSourceRetainedHost.time h J cut) fun (x : Int) (ν : Nat → Int) =>
    And
      (@ThreeSum.LightZetaStages.StoredThrough
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
        ν baseL cut (@ThreeSum.BlockIndexedQuery.leftSource.{u_1} β h J (@Nat.cast.{0} Int instNatCastInt p) B b q)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
      (And
        (@ThreeSum.LightZetaStages.StoredThrough
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
          ν baseR cut
          (@ThreeSum.BlockIndexedQuery.rightSource.{u_2} γ h J (@Nat.cast.{0} Int instNatCastInt p) shift A a q)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
        (Light.Kept μ ν masks)) := by
  exact @ThreeSum.LightBlockSourceRetainedHost.Procs.meets_sourceProof

#print axioms solution
