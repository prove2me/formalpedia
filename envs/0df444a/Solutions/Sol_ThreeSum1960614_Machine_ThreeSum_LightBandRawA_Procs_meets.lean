-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightBandRawA.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:14:21.435979+00:00
-- url     : https://prove2.me/submissions/9aec26d4-9c47-4df6-9522-fadb30d3e335

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle002
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
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
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.Chebyshev
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
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
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
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_for
import Theorems.Thm_Light_seg_append
import Theorems.Thm_Light_seg_cons
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_BandRawA_Stored_keep_before_append
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_BandRawA_row_stored
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandRawAStep_meets

private theorem platform_seg_cons_83c7be2a99 {μ : ℕ → ℤ} {a : ℕ} {x : ℤ} {l : List ℤ} :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a (x :: l) ↔ μ a = x ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ (a + 1) l := by
  exact _root_.Light.seg_cons

private theorem platform_seg_append_83c7be2a99 {μ : ℕ → ℤ} {a : ℕ} {l₁ l₂ : List ℤ} :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a (l₁ ++ l₂) ↔ _root_.ThreeSum1960614.Machine.Light.Seg μ a l₁ ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ (a + l₁.length) l₂ := by
  exact _root_.Light.seg_append

@[simp] private theorem platform_seg_nil_83c7be2a99 (μ : ℕ → ℤ) (a : ℕ) :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a [] := by
  intro i h
  exact (Nat.not_lt_zero i h).elim


namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.LightBandRawA
end ThreeSum.LightBandRawA
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
end ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
namespace ThreeSum1960614.Machine.ThreeSum.BandEnumeration
end ThreeSum1960614.Machine.ThreeSum.BandEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.BandRawA
end ThreeSum1960614.Machine.ThreeSum.BandRawA
namespace ThreeSum1960614.Machine.ThreeSum.LightBandRawA
end ThreeSum1960614.Machine.ThreeSum.LightBandRawA
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

namespace ThreeSum1960614.Machine

/-!
# Consecutive bands of a strictly increasing array

The last band is truncated. Every input position belongs to its quotient
band, the bands are strictly separated, and each band has at most `g` entries.
The quotient in these specifications is realized by `LightBandPartition`.
-/

namespace ThreeSum.BandPartition
open _root_.ThreeSum.BandPartition




















theorem length_le (n g i : ℕ) : _root_.ThreeSum.BandPartition.stop n g i-_root_.ThreeSum.BandPartition.start g i ≤ g := by
  have hle : _root_.ThreeSum.BandPartition.stop n g i ≤ (i+1)*g := min_le_right _ _
  unfold _root_.ThreeSum.BandPartition.start
  simp only [Nat.add_mul,Nat.one_mul] at hle
  omega











end ThreeSum.BandPartition

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## The list of the locals -/







/-- Zeros at the end of the list do not matter. -/
theorem frame_append_zeros (l : List ℤ) (n : ℕ) : _root_.Light.frame (l ++ List.replicate n 0) = _root_.Light.frame l := by
  funext y
  simp only [_root_.Light.frame, List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_replicate]
  split_ifs with h1 h2
  · rfl
  · rw [List.getElem?_eq_none (by omega)]
    rfl
  · rw [List.getElem?_eq_none (by omega)]

/-! ## The value of an expression -/



/-! ## One statement -/

section rules

variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}

















end rules

/-! ## Locals by name, and locals whose values do not matter -/























section
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}







/-! ## A piece of program text with a lemma of its own -/

variable {T T₁ : ℕ} {s s₁ s₂ : _root_.ThreeSum1960614.Machine.Light.Stmt} {Q R : _root_.ThreeSum1960614.Machine.Light.State → Prop}







/-! ## Counting loops with scratch variables -/



end

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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
open _root_.Light


/-! ## Regions -/









/-! ## Memories that agree on some cells -/













variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}



theorem SameOn.refl : _root_.ThreeSum1960614.Machine.Light.SameOn K μ μ := fun _ _ => rfl









/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}















/-! ## The tactics -/











end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Specifications of procedures -/



section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}

/-- From a theorem about a body to the specification. -/
theorem Meets.of_body {args : List ℤ} {Q : ℤ → (ℕ → ℤ) → Prop} {body : _root_.ThreeSum1960614.Machine.Light.Stmt}
    (hp : P[p]? = some body)
    (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d body ⟨_root_.Light.frame args, μ⟩ T fun σ' => Q (σ'.loc 0) σ'.mem) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d args μ T Q :=
  ⟨body, hp, h⟩









end

/-! ## The rule for calls -/

section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List _root_.ThreeSum1960614.Machine.Light.Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} {s : _root_.ThreeSum1960614.Machine.Light.Stmt}









end

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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
open _root_.Light


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp





variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}









@[simp] theorem Seg.nil : _root_.ThreeSum1960614.Machine.Light.Seg μ a [] := fun i h => absurd h (by simp)



/-- Reading a cell of a segment, with a default value for the list. -/
theorem Seg.getD (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) {i : ℕ} (hi : i < l.length) (d : ℤ) : μ (a + i) = l.getD i d := by
  rw [h i hi, List.getD_eq_getElem _ _ hi]











/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : _root_.ThreeSum1960614.Machine.Light.Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]









/-- A segment all of whose cells are kept. -/
theorem Seg.of_sameOn {K : ℕ → Prop} (h : _root_.ThreeSum1960614.Machine.Light.Seg μ b l) (hs : _root_.ThreeSum1960614.Machine.Light.SameOn K μ μ')
    (hK : ∀ i < l.length, K (b + i)) : _root_.ThreeSum1960614.Machine.Light.Seg μ' b l := h.congr fun i hi => hs _ (hK i hi)











































end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The exact physical band-owner record order

There is one four-cell record for every owner-table cell, in BC, AB, AC
rectangle order. A zero flag is a lookup miss. Successful records retain
their physical owner slot even when several owners produce the same triple.
-/

namespace ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandCandidateRows


open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000































theorem cells_length (rs : List _root_.ThreeSum.BandCandidateRows.Record) : (_root_.ThreeSum.BandCandidateRows.cells rs).length=4*rs.length := by
  induction rs with
  | nil => simp [_root_.ThreeSum.BandCandidateRows.cells]
  | cons r rs ih => simp only [_root_.ThreeSum.BandCandidateRows.cells,List.flatMap_cons,List.length_append,_root_.ThreeSum.BandCandidateRows.Record.cells,
      List.length_cons,List.length_nil] at *; omega























end ThreeSum.BandCandidateRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Problems, solvers, and the interpretation of "is solved in time T" in the light language

A *task* is a problem together with a calling convention: which arguments a procedure gets, what the
memory holds when it is called, and what the result and the memory have to be when it returns.
`Solves task P p T need` says that procedure number `p` of the program `P` solves the task within
`T` steps, if the limits of the run allow for `need`.  A reduction of the paper is a *host*: a
procedure that calls an arbitrary solver of another task.

Conventions.

* A solver gets sizes, a bound `U` on the absolute values of the numbers, the addresses of its
  arrays, and as last argument the free pointer `fr`.  All inputs and outputs lie below `fr`.  The
  solver may write its output segments and any cell from `fr` on, and no other cell.  Nothing is
  assumed about the cells from `fr` on, so a solver can be called again and again.
* A solver has to be correct for every valid bound `U` that it is given.
* A solver is a pair of a program and a procedure number.  What is proved about it holds for every
  program that begins with this program, so a host appends its own procedures.

A `Task` is a problem whose time and need depend on a size and a bound.  `TaskN` and `SolvesN` are
the same notions with a list of parameters.
-/

@[expose] public section

namespace Light
open _root_.Light


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp

/-! ## Limits -/









/-! ## Specifications of single routines -/

/-- A list below fr stays where it is if nothing below fr changes. -/
theorem Seg.of_kept {μ μ' : ℕ → ℤ} {a fr : ℕ} {l : List ℤ} (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (hk : _root_.ThreeSum1960614.Machine.Light.Kept μ μ' fr)
    (hle : a + l.length ≤ fr) : _root_.ThreeSum1960614.Machine.Light.Seg μ' a l :=
  h.of_sameOn hk fun i hi => show a + i < fr by omega

/-! ## Tasks and solvers -/





















/-! ## Hosts -/





/-! ## Tasks with a list of parameters -/











end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # List and memory interfaces for the exact candidate record array -/

namespace ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandCandidateRows


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration

set_option maxHeartbeats 1300000









theorem seg_record {μ : ℕ → ℤ} {dst s : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record}
    (H : _root_.ThreeSum1960614.Machine.Light.Seg μ dst (_root_.ThreeSum.BandCandidateRows.cells rs)) (hs : s < rs.length) :
    _root_.ThreeSum1960614.Machine.Light.Seg μ (dst+4*s) (rs.getD s default).cells := by
  intro j hj
  have hj4 : j < 4 := by simpa [_root_.ThreeSum.BandCandidateRows.Record.cells] using hj
  have hi : s*4+j < (_root_.ThreeSum.BandCandidateRows.cells rs).length := by rw [_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.cells_length]; omega
  have he := H.getD hi 0
  rw [_root_.ThreeSum.BandCandidateRows.cells,_root_.ThreeSum.OutputDecodeOrder.getD_flatMap_uniform rs _root_.ThreeSum.BandCandidateRows.Record.cells 4
    (by intro r _; rfl) default 0 hs hj4,List.getD_eq_getElem _ _ hj] at he
  simpa only [Nat.mul_comm s 4,Nat.add_assoc] using he





theorem record_fields {μ : ℕ → ℤ} {dst : ℕ} {r : _root_.ThreeSum.BandCandidateRows.Record}
    (H : _root_.ThreeSum1960614.Machine.Light.Seg μ dst r.cells) :
    μ dst=(r.flag : ℤ) ∧ μ (dst+1)=(r.a : ℤ) ∧
      μ (dst+2)=(r.b : ℤ) ∧ μ (dst+3)=(r.c : ℤ) := by
  simpa [_root_.ThreeSum.BandCandidateRows.Record.cells,platform_seg_cons_83c7be2a99,Nat.add_assoc] using H

end ThreeSum.BandCandidateRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact A-value incidences of the physical band-owner catalog

Each successful owner contributes only its A band. Labels retain the
physical owner slot and the coordinate in the retained sorted A array.
Equal values and equal triples in different owner slots remain distinct.
-/

namespace ThreeSum.BandRawA
open _root_.ThreeSum.BandRawA


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition

set_option maxHeartbeats 1600000
set_option maxRecDepth 7000



















theorem row_length (n g owner : ℕ) (r : _root_.ThreeSum.BandCandidateRows.Record) :
    (_root_.ThreeSum.BandRawA.row n g owner r).length=if r.flag=1 then _root_.ThreeSum.BandRawA.bandLength n g r.a else 0 := by
  unfold _root_.ThreeSum.BandRawA.row
  split_ifs <;> simp

theorem row_length_le (n g owner : ℕ) (r : _root_.ThreeSum.BandCandidateRows.Record) : (_root_.ThreeSum.BandRawA.row n g owner r).length ≤ g := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.row_length]
  split_ifs
  · exact _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.length_le n g r.a
  · omega





theorem firstRows_succ (n g : ℕ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) (i : ℕ) :
    _root_.ThreeSum.BandRawA.firstRows n g rs (i+1)=_root_.ThreeSum.BandRawA.firstRows n g rs i++_root_.ThreeSum.BandRawA.row n g i (rs.getD i default) := by
  simp only [_root_.ThreeSum.BandRawA.firstRows,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]

@[simp] theorem count_zero (n g : ℕ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) : _root_.ThreeSum.BandRawA.count n g rs 0=0 := rfl

theorem count_succ (n g : ℕ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) (i : ℕ) :
    _root_.ThreeSum.BandRawA.count n g rs (i+1)=_root_.ThreeSum.BandRawA.count n g rs i+(_root_.ThreeSum.BandRawA.row n g i (rs.getD i default)).length := by
  simp only [_root_.ThreeSum.BandRawA.count,_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.firstRows_succ,List.length_append]



theorem count_bound (n g : ℕ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) (i : ℕ) : _root_.ThreeSum.BandRawA.count n g rs i ≤ g*i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.count_succ]
    have hh := _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.row_length_le n g i (rs.getD i default)
    nlinarith

























end ThreeSum.BandRawA

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # The three retained parallel arrays of A-value incidences -/

namespace ThreeSum.BandRawA
open _root_.ThreeSum.BandRawA


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows

set_option maxHeartbeats 1400000



theorem Stored.empty (μ : ℕ → ℤ) (vals owners positions : ℕ) (f : ℕ → ℤ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.Stored μ vals owners positions f [] := ⟨by simp [_root_.ThreeSum.BandRawA.values],by simp [_root_.ThreeSum.BandRawA.ownerLabels],by simp [_root_.ThreeSum.BandRawA.positionLabels]⟩

theorem Stored.append {μ : ℕ → ℤ} {vals owners positions : ℕ} {f : ℕ → ℤ} {as bs : List _root_.ThreeSum.BandRawA.Label}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.Stored μ vals owners positions f as)
    (K : _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.Stored μ (vals+as.length) (owners+as.length) (positions+as.length) f bs) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.Stored μ vals owners positions f (as++bs) := by
  constructor
  · rw [_root_.ThreeSum.BandRawA.values,List.map_append]
    exact platform_seg_append_83c7be2a99.mpr ⟨H.valueRows,by simpa only [_root_.ThreeSum.BandRawA.values,List.length_map] using K.valueRows⟩
  · rw [_root_.ThreeSum.BandRawA.ownerLabels,List.map_append]
    exact platform_seg_append_83c7be2a99.mpr ⟨H.ownerRows,by simpa only [_root_.ThreeSum.BandRawA.ownerLabels,List.length_map] using K.ownerRows⟩
  · rw [_root_.ThreeSum.BandRawA.positionLabels,List.map_append]
    exact platform_seg_append_83c7be2a99.mpr ⟨H.positionRows,by simpa only [_root_.ThreeSum.BandRawA.positionLabels,List.length_map] using K.positionRows⟩

theorem row_position_lt {n g owner j : ℕ} {r : _root_.ThreeSum.BandCandidateRows.Record}
    (hj : j < (_root_.ThreeSum.BandRawA.row n g owner r).length) : _root_.ThreeSum.BandPartition.start g r.a+j < n := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.row_length] at hj
  split_ifs at hj with hf
  · have hh := _root_.ThreeSum.BandPartition.stop_le n g r.a
    unfold _root_.ThreeSum.BandRawA.bandLength at hj
    omega
  · omega







end ThreeSum.BandRawA

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawA

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
set_option maxHeartbeats 2200000
set_option maxRecDepth 8000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {records src n g vals : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record} {f : ℕ → ℤ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightBandRawA.Procs.meets__implementation_1d5c1bcfde {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawA.Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth) (hg : 0 < g)
    (hrecords : records+4*rs.length ≤ vals) (hsrc : src+n ≤ vals)
    (hspace : _root_.ThreeSum.LightBandRawA.space vals rs.length g ≤ lim.space)
    (hword : (_root_.ThreeSum.LightBandRawA.word n g rs.length : ℤ) ≤ lim.word)
    (hvalid : ∀ i < rs.length, (rs.getD i default).flag=1 →
      (rs.getD i default).a < _root_.ThreeSum.BandPartition.size n g)
    (hrecordRead : _root_.ThreeSum1960614.Machine.Light.Seg μ records (_root_.ThreeSum.BandCandidateRows.cells rs))
    (hread : ∀ j < n, μ (src+j)=f j) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [records,rs.length,src,n,g,vals] μ (_root_.ThreeSum.LightBandRawA.time rs.length g)
      (fun r ν => r=((_root_.ThreeSum.BandRawA.items n g rs).length : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.Stored ν vals (_root_.ThreeSum.LightBandRawA.ownerBase vals rs.length g) (_root_.ThreeSum.LightBandRawA.positionBase vals rs.length g)
          f (_root_.ThreeSum.BandRawA.items n g rs) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν vals) := by
  have hspace' : vals+_root_.ThreeSum.LightBandRawA.capacity rs.length g+_root_.ThreeSum.LightBandRawA.capacity rs.length g+_root_.ThreeSum.LightBandRawA.capacity rs.length g ≤ lim.space := hspace
  have hcapWord : (g : ℤ)*(rs.length : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show _root_.ThreeSum.LightBandRawA.capacity rs.length g ≤ lim.space by omega) :
      (g : ℤ)*(rs.length : ℤ) ≤ (lim.space : ℤ)).trans hw
  have hcapNonneg : (0 : ℤ) ≤ (g : ℤ)*(rs.length : ℤ) := by positivity
  have hnWord : (n : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold _root_.ThreeSum.LightBandRawA.word; omega : n ≤ word n g rs.length)).trans hword
  have hgWord : (g : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold _root_.ThreeSum.LightBandRawA.word; omega : g ≤ word n g rs.length)).trans hword
  have hNWord : (rs.length : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold _root_.ThreeSum.LightBandRawA.word; omega : rs.length ≤ word n g rs.length)).trans hword
  have howner : _root_.ThreeSum.LightBandRawA.ownerBase vals rs.length g+_root_.ThreeSum.LightBandRawA.capacity rs.length g=_root_.ThreeSum.LightBandRawA.positionBase vals rs.length g := rfl
  have hvalues : vals+_root_.ThreeSum.LightBandRawA.capacity rs.length g=_root_.ThreeSum.LightBandRawA.ownerBase vals rs.length g := rfl
  have hposition : _root_.ThreeSum.LightBandRawA.positionBase vals rs.length g+_root_.ThreeSum.LightBandRawA.capacity rs.length g ≤ lim.space := hspace
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body S.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawA.body _root_.ThreeSum.LightBandRawA.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightBandRawA.capacity rs.length g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBandRawA.capacity]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBandRawA.capacity] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBandRawA.capacity] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightBandRawA.ownerBase vals rs.length g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBandRawA.ownerBase]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBandRawA.ownerBase] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBandRawA.ownerBase] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightBandRawA.positionBase vals rs.length g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBandRawA.positionBase]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBandRawA.positionBase] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBandRawA.positionBase] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  refine _root_.ThreeSum1960614.Machine.Light.Ends.pieceThen (_root_.ThreeSum1960614.Machine.Light.Ends.for
    (T := rs.length*(_root_.ThreeSum.LightBandRawAStep.time g+200)+6)
    (Q := _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawA.Inv μ rs f records src n g vals rs.length)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawA.Inv μ rs f records src n g vals) rs.length
    (_root_.ThreeSum.LightBandRawAStep.time g+192) ?start ?round ?done ?bound) ?finish
  case start =>
    refine ⟨0,0,μ,?_,_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.Stored.empty _ _ _ _ _,_root_.ThreeSum1960614.Machine.Light.SameOn.refl⟩
    simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.count_zero]
    simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]
    exact (_root_.ThreeSum1960614.Machine.Light.frame_append_zeros [records,rs.length,src,n,g,vals,_root_.ThreeSum.LightBandRawA.capacity rs.length g,
      _root_.ThreeSum.LightBandRawA.ownerBase vals rs.length g,_root_.ThreeSum.LightBandRawA.positionBase vals rs.length g,0,0] 2).symm
  case round =>
    rintro i _ hi _ ⟨flag,a,ν,rfl,stored,kept⟩
    have hnext : _root_.ThreeSum.BandRawA.count n g rs (i+1) ≤ _root_.ThreeSum.LightBandRawA.capacity rs.length g := by
      have hb := _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.count_bound n g rs (i+1)
      have hm := Nat.mul_le_mul_left g (show i+1 ≤ rs.length by omega)
      exact hb.trans hm
    have hfit : _root_.ThreeSum.BandRawA.count n g rs i+(_root_.ThreeSum.BandRawA.row n g i (rs.getD i default)).length ≤ _root_.ThreeSum.LightBandRawA.capacity rs.length g := by
      rwa [_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.count_succ] at hnext
    have hstored : _root_.ThreeSum1960614.Machine.Light.Seg ν records (_root_.ThreeSum.BandCandidateRows.cells rs) :=
      hrecordRead.of_kept kept (by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.cells_length] using hrecords)
    have hfields := _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.record_fields (_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.seg_record hstored hi)
    have hflag := hfields.1
    have hA := hfields.2.1
    have hstepWord : ((n+g+i+10 : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (by unfold _root_.ThreeSum.LightBandRawA.word; omega : n+g+i+10 ≤ word n g rs.length)).trans hword
    have hflagAddr : ((records : ℤ)+4*(i : ℤ)).toNat=records+4*i := by omega
    have hAAddr : ((records : ℤ)+4*(i : ℤ)+1).toNat=records+4*i+1 := by omega
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen ((rs.getD i default).flag : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hflagAddr, hflag]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hflagAddr, hflag] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hflagAddr, hflag] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen ((rs.getD i default).a : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hAAddr, hA]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hAAddr, hA] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hAAddr, hA] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    have hc := _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawAStep.meets (d := d+1) (μ := ν)
      (src := src) (n := n) (g := g) (owner := i) (r := rs.getD i default)
      (values := vals) (owners := _root_.ThreeSum.LightBandRawA.ownerBase vals rs.length g)
      (positions := _root_.ThreeSum.LightBandRawA.positionBase vals rs.length g) (previous := _root_.ThreeSum.BandRawA.count n g rs i)
      (capacity := _root_.ThreeSum.LightBandRawA.capacity rs.length g) S.step S.row S.copy S.fill hw (by omega) hg
      (hvalid i hi) hsrc hvalues.le howner.le hposition hfit hstepWord
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       first
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
       on_goal -1 => (rintro result ν₁ ⟨hresult, hout, hkeep⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    have hresult' : result=(_root_.ThreeSum.BandRawA.count n g rs (i+1) : ℤ) := by
      simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.count_succ] using hresult
    have hold : _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.Stored ν₁ vals (_root_.ThreeSum.LightBandRawA.ownerBase vals rs.length g) (_root_.ThreeSum.LightBandRawA.positionBase vals rs.length g)
        f (_root_.ThreeSum.BandRawA.firstRows n g rs i) :=
      stored.keep_before_append hkeep hvalues.le howner.le hfit
    have hrowStored : _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.Stored ν₁ (vals+_root_.ThreeSum.BandRawA.count n g rs i)
        (_root_.ThreeSum.LightBandRawA.ownerBase vals rs.length g+_root_.ThreeSum.BandRawA.count n g rs i)
        (_root_.ThreeSum.LightBandRawA.positionBase vals rs.length g+_root_.ThreeSum.BandRawA.count n g rs i) f (_root_.ThreeSum.BandRawA.row n g i (rs.getD i default)) := by
      apply _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.row_stored
      intro j hj
      have hp := _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.row_position_lt hj
      refine ⟨?_,(hout j hj).2.1,(hout j hj).2.2⟩
      rw [(hout j hj).1,kept _ (by omega)]
      simpa only [Nat.add_assoc] using hread _ hp
    refine ⟨by simp,(rs.getD i default).flag,(rs.getD i default).a,ν₁,?_,?_,?_⟩
    · simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal,hresult']
    · rw [_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.firstRows_succ]
      exact hold.append hrowStored
    · intro addr ha
      rw [hkeep addr ⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega)⟩,kept addr ha]
  case done =>
    rintro _ _ ⟨flag,a,ν,rfl,stored,kept⟩
    exact ⟨flag,a,ν,rfl,stored,kept⟩
  case bound =>
    rintro i _ _ _ ⟨flag,a,ν,rfl,_,_⟩
    (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
  case finish =>
    rintro _ ⟨flag,a,ν,rfl,stored,kept⟩
    have hc := _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.count_bound n g rs rs.length
    have hcWord : (_root_.ThreeSum.BandRawA.count n g rs rs.length : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (show _root_.ThreeSum.BandRawA.count n g rs rs.length ≤ lim.space by
        change _root_.ThreeSum.BandRawA.count n g rs rs.length ≤ _root_.ThreeSum.LightBandRawA.capacity rs.length g at hc
        omega)).trans hw
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.BandRawA.count n g rs rs.length : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    exact ⟨rfl,stored,kept⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightBandRawA.Procs.meets__implementation_1d5c1bcfde) := (@ThreeSum1960614.Machine.ThreeSum.LightBandRawA.Procs.meets__implementation_1d5c1bcfde)

#print axioms solution
