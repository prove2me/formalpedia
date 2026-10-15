-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightBlockMasks.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:13:38.356199+00:00
-- url     : https://prove2.me/submissions/722ce107-37e1-43e4-82ab-3b33aecd1dba

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Lean
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
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_powTable_ends
import Theorems.Thm_Light_seg_append
import Theorems.Thm_Light_seg_cons

private theorem platform_seg_cons_1c7af2109e {μ : ℕ → ℤ} {a : ℕ} {x : ℤ} {l : List ℤ} :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a (x :: l) ↔ μ a = x ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ (a + 1) l := by
  exact _root_.Light.seg_cons

private theorem platform_seg_append_1c7af2109e {μ : ℕ → ℤ} {a : ℕ} {l₁ l₂ : List ℤ} :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a (l₁ ++ l₂) ↔ _root_.ThreeSum1960614.Machine.Light.Seg μ a l₁ ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ (a + l₁.length) l₂ := by
  exact _root_.Light.seg_append

@[simp] private theorem platform_seg_nil_1c7af2109e (μ : ℕ → ℤ) (a : ℕ) :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a [] := by
  intro i h
  exact (Nat.not_lt_zero i h).elim


namespace Finset
end Finset
namespace Light
end Light
namespace Light.PowTable
end Light.PowTable
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockMaskLayout
end ThreeSum.BlockMaskLayout
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.LightBlockMasks
end ThreeSum.LightBlockMasks
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.MaskDifference
end ThreeSum.MaskDifference
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.PowTable
end ThreeSum1960614.Machine.Light.PowTable
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
end ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockMasks
end ThreeSum1960614.Machine.ThreeSum.LightBlockMasks
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.MaskDifference
end ThreeSum1960614.Machine.ThreeSum.MaskDifference
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

namespace ThreeSum1960614.Machine

/-!
# Flattening a block family of subsets

The coordinates retain the block index explicitly. Joining and slicing are
mutually inverse, preserve Boolean set operations, and give exact cardinalities
for balanced full inputs and forced prefixes.
-/

namespace ThreeSum.BlockRows
open _root_.ThreeSum.BlockRows


open _root_.Finset
open scoped _root_.BigOperators















































@[simp] theorem mem_prefixIndices {J k : ℕ} {i : Fin J} :
    i ∈ _root_.ThreeSum.BlockRows.prefixIndices J k ↔ i.val < k := by simp [_root_.ThreeSum.BlockRows.prefixIndices]



end ThreeSum.BlockRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact arithmetic subtraction of one subset mask from another -/

namespace ThreeSum.MaskDifference
open _root_.ThreeSum.MaskDifference


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress

theorem subsetMask_sum {L : ℕ} (S : Finset (Fin L)) :
    _root_.ThreeSum.SubsetAddress.subsetMask S = ∑ i ∈ S, 2^i.val := by
  simp [_root_.ThreeSum.SubsetAddress.subsetMask,_root_.ThreeSum.SubsetAddress.maskOf,_root_.ThreeSum.SubsetAddress.natPositions]











end ThreeSum.MaskDifference

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Runs -/









/-! ## The rules -/





























/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/


















/-! ## Simplification -/

attribute [simp] _root_.ThreeSum1960614.Machine.Light.Expr.val _root_.ThreeSum1960614.Machine.Light.Expr.cost _root_.ThreeSum1960614.Machine.Light.Expr.Safe _root_.Light.Op.eval _root_.ThreeSum1960614.Machine.Light.Cond.Holds _root_.ThreeSum1960614.Machine.Light.Cond.cost _root_.ThreeSum1960614.Machine.Light.Cond.Safe _root_.Light.frame





/-- The natural number behind an address that is a sum of two natural numbers. -/
@[simp] theorem toNat_natCast_add_natCast (a b : ℕ) : ((a : ℤ) + (b : ℤ)).toNat = a + b := by
  rw [← Nat.cast_add, Int.toNat_natCast]

/-! ## The limits -/









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
# Explicit row-major encoding of the block ground set

Block coordinates are numbered by `block * width + coordinate`. The
equivalence connects compact machine-mask tables on `Fin (J*L)` with the
sigma-typed block sets in the reporting proof. Flattened one-hot coefficients
already include their positional radix factors.
-/

namespace ThreeSum.BlockIndex
open _root_.ThreeSum.BlockIndex


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open scoped _root_.BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false



@[simp] theorem coordEquiv_val {J L : ℕ} (i : Fin J) (x : Fin L) :
    (_root_.ThreeSum.BlockIndex.coordEquiv J L ⟨i,x⟩).val = i.val*L+x.val := by
  simp [_root_.ThreeSum.BlockIndex.coordEquiv, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]































end ThreeSum.BlockIndex

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















/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : _root_.ThreeSum1960614.Machine.Light.Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]





/-- Writing outside a segment. -/
theorem Seg.update_out (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (hb : b < a ∨ a + l.length ≤ b) (x : ℤ) :
    _root_.ThreeSum1960614.Machine.Light.Seg (Function.update μ b x) a l :=
  h.congr fun i hi => Function.update_of_ne (by omega) _ _

/-- Writing just after a segment makes it longer. -/
theorem Seg.snoc (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (x : ℤ) : _root_.ThreeSum1960614.Machine.Light.Seg (Function.update μ (a + l.length) x) a (l ++ [x]) :=
  platform_seg_append_1c7af2109e.2 ⟨h.update_out (Or.inr le_rfl) x, by simp [platform_seg_cons_1c7af2109e]⟩



















/-- Reading a cell of a segment of natural numbers, with the proof that the index is in range. -/
theorem SegN.getElem {l : List ℕ} (h : _root_.ThreeSum1960614.Machine.Light.SegN μ a l) {i : ℕ} (hi : i < l.length) :
    μ (a + i) = (l[i] : ℕ) := by
  rw [h i (by simpa using hi), List.getElem_map]

/-- Writing just after a segment of natural numbers makes it longer. -/
theorem SegN.snoc {l : List ℕ} (h : _root_.ThreeSum1960614.Machine.Light.SegN μ a l) (x : ℕ) :
    _root_.ThreeSum1960614.Machine.Light.SegN (Function.update μ (a + l.length) (x : ℤ)) a (l ++ [x]) := by
  simpa [_root_.ThreeSum1960614.Machine.Light.SegN] using _root_.ThreeSum1960614.Machine.Light.Seg.snoc h (x : ℤ)























end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact row-major mask packing and prefix scan invariants -/

namespace ThreeSum.BlockMaskLayout
open _root_.ThreeSum.BlockMaskLayout


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open scoped _root_.BigOperators





theorem mask_join {J L : ℕ} (I : Finset (Fin J)) (rows : Fin J → Finset (Fin L)) :
    _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndex.indexSet (_root_.ThreeSum.BlockRows.join I rows)) = ∑ i ∈ I, _root_.ThreeSum.BlockMaskLayout.rowMask rows i := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.MaskDifference.subsetMask_sum]
  unfold _root_.ThreeSum.BlockIndex.indexSet
  rw [Finset.sum_map]
  unfold _root_.ThreeSum.BlockRows.join
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Equiv.toEmbedding_apply,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.coordEquiv_val,pow_add,_root_.ThreeSum.BlockMaskLayout.rowMask,
    _root_.ThreeSum1960614.Machine.ThreeSum.MaskDifference.subsetMask_sum,Finset.mul_sum]

theorem prefixMask_eq_sum {J L : ℕ} (rows : Fin J → Finset (Fin L)) (k : ℕ) :
    _root_.ThreeSum.BlockMaskLayout.prefixMask rows k = ∑ i ∈ _root_.ThreeSum.BlockRows.prefixIndices J k, _root_.ThreeSum.BlockMaskLayout.rowMask rows i := _root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout.mask_join _ _

@[simp] theorem prefixMask_zero {J L : ℕ} (rows : Fin J → Finset (Fin L)) :
    _root_.ThreeSum.BlockMaskLayout.prefixMask rows 0 = 0 := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout.prefixMask_eq_sum]
  simp [_root_.ThreeSum.BlockRows.prefixIndices]

theorem prefixIndices_succ {J k : ℕ} (hk : k < J) :
    _root_.ThreeSum.BlockRows.prefixIndices J (k+1) = insert ⟨k,hk⟩ (_root_.ThreeSum.BlockRows.prefixIndices J k) := by
  ext i
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_prefixIndices,Finset.mem_insert,Fin.ext_iff]
  omega

theorem prefixMask_succ {J L k : ℕ} (rows : Fin J → Finset (Fin L)) (hk : k < J) :
    _root_.ThreeSum.BlockMaskLayout.prefixMask rows (k+1) = _root_.ThreeSum.BlockMaskLayout.prefixMask rows k+_root_.ThreeSum.BlockMaskLayout.rowMask rows ⟨k,hk⟩ := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout.prefixMask_eq_sum,_root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout.prefixIndices_succ hk,Finset.sum_insert (by simp),_root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout.prefixMask_eq_sum]
  exact Nat.add_comm _ _

@[simp] theorem prefixMask_all {J L : ℕ} (rows : Fin J → Finset (Fin L)) :
    _root_.ThreeSum.BlockMaskLayout.prefixMask rows J = _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndex.indexSet (_root_.ThreeSum.BlockRows.flat rows)) := by
  have he : _root_.ThreeSum.BlockRows.prefixIndices J J = univ := by
    ext i
    simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_prefixIndices,Finset.mem_univ,iff_true]
    exact i.isLt
  simp only [_root_.ThreeSum.BlockMaskLayout.prefixMask,he,_root_.ThreeSum.BlockRows.flat]

theorem prefixMask_lt {J L : ℕ} (rows : Fin J → Finset (Fin L)) (k : ℕ) :
    _root_.ThreeSum.BlockMaskLayout.prefixMask rows k < 2^(J*L) := (_root_.ThreeSum.SubsetAddress.subsetMask_isMask _).1

theorem rowMask_lt {J L : ℕ} (rows : Fin J → Finset (Fin L)) (i : Fin J) :
    _root_.ThreeSum.BlockMaskLayout.rowMask rows i < 2^(J*L) := by
  have he : _root_.ThreeSum.BlockMaskLayout.prefixMask rows (i.val+1) = _root_.ThreeSum.BlockMaskLayout.prefixMask rows i.val+_root_.ThreeSum.BlockMaskLayout.rowMask rows i :=
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout.prefixMask_succ rows i.isLt
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout.prefixMask_lt rows (i.val+1)
  omega





@[simp] theorem rawMasks_length {J L : ℕ} (rows : Fin J → Finset (Fin L)) :
    (_root_.ThreeSum.BlockMaskLayout.rawMasks rows).length = J := by simp [_root_.ThreeSum.BlockMaskLayout.rawMasks]

@[simp] theorem packedMasks_length {J L : ℕ} (rows : Fin J → Finset (Fin L)) :
    (_root_.ThreeSum.BlockMaskLayout.packedMasks rows).length = J := by simp [_root_.ThreeSum.BlockMaskLayout.packedMasks]

theorem packedMasks_take_succ {J L j : ℕ} (rows : Fin J → Finset (Fin L)) (hj : j < J) :
    (_root_.ThreeSum.BlockMaskLayout.packedMasks rows).take (j+1) = (_root_.ThreeSum.BlockMaskLayout.packedMasks rows).take j ++ [_root_.ThreeSum.BlockMaskLayout.rowMask rows ⟨j,hj⟩] := by
  rw [List.take_succ_eq_append_getElem (by simpa using hj)]
  simp [_root_.ThreeSum.BlockMaskLayout.packedMasks]

end ThreeSum.BlockMaskLayout

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
# Tables of powers

powTable(dst, L, b) writes 1, b, b², …, b^(L-1) into the L cells from dst and changes nothing else,
within `powTableTime L` steps (`powTable_meets`).  The list of these powers is `powList b L`.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



@[simp] theorem length_powList (b L : ℕ) : (_root_.Light.powList b L).length = L := by simp [_root_.Light.powList]

@[simp] theorem getElem_powList {b L j : ℕ} (h : j < (_root_.Light.powList b L).length) :
    (_root_.Light.powList b L)[j] = ((b ^ j : ℕ) : ℤ) := by
  simp [_root_.Light.powList]

namespace PowTable
open _root_.Light.PowTable








end PowTable

open _root_.Light.PowTable
open _root_.ThreeSum1960614.Machine.Light.PowTable











/-- **powTable(dst, L, b)** writes the powers 1, b, …, b^(L-1) into the L cells from dst and changes
nothing else. -/
theorem powTable_meets {p : ℕ} (hp : P[p]? = some _root_.ThreeSum1960614.Machine.Light.powTableBody) {μ : ℕ → ℤ} {dst L b : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + L ≤ lim.space)
    (hpow : ∀ j ≤ L, ((b ^ j : ℕ) : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [(dst : ℤ), L, b] μ (_root_.Light.powTableTime L) fun _ μ' =>
      _root_.ThreeSum1960614.Machine.Light.Seg μ' dst (_root_.Light.powList b L) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst L :=
  -- the local variables that are no arguments hold 0
  _root_.ThreeSum1960614.Machine.Light.Meets.of_body hp (_root_.ThreeSum1960614.Machine.Light.frame_append_zeros [(dst : ℤ), L, b] 2 ▸ _root_.ThreeSum1960614.Machine.Light.powTable_ends 0 0 [] hw hdst hpow)

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Machine evaluation of compact subset addresses

The current width decreases by one in each recursive call. Its highest
power of two is read from a table, so neither division nor a loop proportional
to the numeric bit-mask value occurs. Pascal coefficients are single reads
from the constructed rectangular table.
-/

namespace ThreeSum.LightSubsetAddress
open _root_.ThreeSum.LightSubsetAddress


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}



theorem powers_of_segment {μ : ℕ → ℤ} {base W : ℕ}
    (h : _root_.ThreeSum1960614.Machine.Light.Seg μ base (_root_.Light.powList 2 (W+1))) : _root_.ThreeSum.LightSubsetAddress.Powers μ base W := by
  intro i hi
  have hs := h i (by simp; omega)
  simpa only [_root_.ThreeSum1960614.Machine.Light.getElem_powList] using hs













end ThreeSum.LightSubsetAddress

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBlockMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockMasks

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockMaskLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightBlockMasks.meets__implementation_e08124e141 {pMain pPowers : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockMasks.body pPowers)) (hPowers : P[pPowers]? = some _root_.ThreeSum1960614.Machine.Light.powTableBody)
    {μ : ℕ → ℤ} {J L src dst work d : ℕ} (rows : Fin J → Finset (Fin L))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+J ≤ work) (hdst : dst+J ≤ work) (hsep : _root_.Light.Apart src J dst J)
    (hspace : work+(L+1) ≤ lim.space)
    (hword : ((2^(J*L+1) : ℕ) : ℤ) ≤ lim.word)
    (hread : _root_.ThreeSum1960614.Machine.Light.SegN μ src (_root_.ThreeSum.BlockMaskLayout.rawMasks rows)) (hd : d+1 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [J,L,src,dst,work] μ (_root_.ThreeSum.LightBlockMasks.time J L)
      (fun r μ' => r = (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndex.indexSet (_root_.ThreeSum.BlockRows.flat rows)) : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' dst (_root_.ThreeSum.BlockMaskLayout.packedMasks rows) ∧ _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' work dst J) := by
  have hbase : (2 : ℤ) ≤ lim.word := by
    have hh : (2^1 : ℕ) ≤ 2^(J*L+1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (by exact_mod_cast hh : (2 : ℤ) ≤ ((2^(J*L+1) : ℕ) : ℤ)).trans hword
  have hpower (a : ℕ) (ha : a ≤ J*L+1) : ((2^a : ℕ) : ℤ) ≤ lim.word := by
    have hh : (2^a : ℕ) ≤ 2^(J*L+1) := Nat.pow_le_pow_right (by decide) ha
    exact (by exact_mod_cast hh : ((2^a : ℕ) : ℤ) ≤ ((2^(J*L+1) : ℕ) : ℤ)).trans hword
  have hprefix (j : ℕ) : (_root_.ThreeSum.BlockMaskLayout.prefixMask rows j : ℤ) ≤ lim.word := by
    have hh : _root_.ThreeSum.BlockMaskLayout.prefixMask rows j ≤ 2^(J*L+1) :=
      (Nat.le_of_lt (_root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout.prefixMask_lt rows j)).trans (Nat.pow_le_pow_right (by decide) (by omega))
    exact (by exact_mod_cast hh : (prefixMask rows j : ℤ) ≤ ((2^(J*L+1) : ℕ) : ℤ)).trans hword
  have hrow (i : Fin J) : (_root_.ThreeSum.BlockMaskLayout.rowMask rows i : ℤ) ≤ lim.word := by
    have hh : _root_.ThreeSum.BlockMaskLayout.rowMask rows i ≤ 2^(J*L+1) :=
      (Nat.le_of_lt (_root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout.rowMask_lt rows i)).trans (Nat.pow_le_pow_right (by decide) (by omega))
    exact (by exact_mod_cast hh : (rowMask rows i : ℤ) ≤ ((2^(J*L+1) : ℕ) : ℤ)).trans hword
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockMasks.body _root_.ThreeSum.LightBlockMasks.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.iteIffThen ((0 : ℤ) < (J : ℤ)) (fun hJpos => ?_) (fun hJzero => ?_) ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.Light.powTableTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.Light.powTableTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.Light.powTableTime] <;> omega)
     all_goals
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
  · have hJ : 0 < J := by exact_mod_cast hJpos
    have hL : L ≤ J*L := Nat.le_mul_of_pos_left _ hJ
    have hradix := hpower L (by omega)
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockMasks.nonemptyBody
    have hp := _root_.ThreeSum1960614.Machine.Light.powTable_meets (d := d+1) (μ := μ) (dst := work)
      (L := L+1) (b := 2) hPowers hw hspace (by intro i hi; exact hpower i (by omega))
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hp _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hp ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.Light.powTableTime]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.Light.powTableTime] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.Light.powTableTime] <;> omega)
       on_goal -1 => (rintro powRet μ₁ ⟨hpow, hkept⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    have hpowers := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress.powers_of_segment hpow
    have hradixRead := hpowers L le_rfl
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (2 ^ L : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hradixRead, _root_.Light.powTableTime]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hradixRead, _root_.Light.powTableTime] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hradixRead, _root_.Light.powTableTime] <;> omega)
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
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (1 : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.Light.powTableTime]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.Light.powTableTime] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.Light.powTableTime] <;> omega)
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
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.Light.powTableTime]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.Light.powTableTime] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.Light.powTableTime] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    (repeat
       with_unfolding_none
         first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
    refine _root_.ThreeSum1960614.Machine.Light.Ends.pieceThen (_root_.ThreeSum1960614.Machine.Light.Ends.for (lim := lim) (P := P) (d := d) (i := 9) (hi := _root_.ThreeSum1960614.Machine.Light.v 0) (body := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockMasks.roundBody)
      (T := J*130+20) (Q := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockMasks.Inv μ rows src dst work powRet J)
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockMasks.Inv μ rows src dst work powRet) J 110
      ?start ?round ?done ?bound (hT := by (first
                                            | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                first
                                                | omega
                                                | (ring_nf; omega))
                                            | omega
                                            |
                                              (simp [] <;>
                                                  first
                                                  | omega
                                                  | (ring_nf; omega))))) ?after
    case start =>
      refine ⟨0,μ₁,?_,by simp [_root_.ThreeSum1960614.Machine.Light.SegN],hpowers,?_⟩
      · simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]
        change _root_.Light.frame [(J : ℤ),L,src,dst,work,powRet,2^L,1,0,0] =
          _root_.Light.frame ([(J : ℤ),L,src,dst,work,powRet,2^L,1,0,0] ++ [0])
        exact (_root_.ThreeSum1960614.Machine.Light.frame_append_zeros _ 1).symm
      · intro i hi
        exact hkept i (Or.inl hi.1)
    case round =>
      rintro j _ hj _ ⟨r,μ',rfl,hseg,hpowers',hkeep⟩
      have hnextPrefix := hprefix (j+1)
      have hrowWord := hrow ⟨j,hj⟩
      have hmul := Nat.mul_le_mul_right L (show j+1 ≤ J by omega)
      have hnextFactor := hpower ((j+1)*L) (by omega)
      have hnextFactorInt : (2 : ℤ)^((j+1)*L) ≤ lim.word := by
        simpa only [Nat.cast_pow,Nat.cast_ofNat] using hnextFactor
      have hmread : μ' (src+j) = (_root_.ThreeSum.SubsetAddress.subsetMask (rows ⟨j,hj⟩) : ℤ) := by
        rw [hkeep _ ⟨by omega,by omega⟩]
        have hr := hread.getElem (by simpa using hj)
        simpa only [_root_.ThreeSum.BlockMaskLayout.rawMasks,List.getElem_ofFn] using hr
      have hprod : (_root_.ThreeSum.SubsetAddress.subsetMask (rows ⟨j,hj⟩) : ℤ)*((2^(j*L) : ℕ) : ℤ) =
          (_root_.ThreeSum.BlockMaskLayout.rowMask rows ⟨j,hj⟩ : ℤ) := by simp [_root_.ThreeSum.BlockMaskLayout.rowMask,mul_comm]
      have hprodInt : (_root_.ThreeSum.SubsetAddress.subsetMask (rows ⟨j,hj⟩) : ℤ)*2^(j*L) =
          (_root_.ThreeSum.BlockMaskLayout.rowMask rows ⟨j,hj⟩ : ℤ) := by
        simpa only [Nat.cast_pow,Nat.cast_ofNat] using hprod
      have hsum : (_root_.ThreeSum.BlockMaskLayout.prefixMask rows j : ℤ)+(_root_.ThreeSum.BlockMaskLayout.rowMask rows ⟨j,hj⟩ : ℤ) =
          (_root_.ThreeSum.BlockMaskLayout.prefixMask rows (j+1) : ℤ) := by exact_mod_cast (_root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout.prefixMask_succ rows hj).symm
      have hfactor : ((2^(j*L) : ℕ) : ℤ)*((2^L : ℕ) : ℤ) = ((2^((j+1)*L) : ℕ) : ℤ) := by
        norm_cast
        rw [← pow_add,Nat.succ_mul]
      have hfactorInt : (2 : ℤ)^(j*L)*2^L = ((2^((j+1)*L) : ℕ) : ℤ) := by
        simpa only [Nat.cast_pow,Nat.cast_ofNat] using hfactor
      unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockMasks.roundBody
      (focus
         ((first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
           repeat
             with_unfolding_none
               first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
         refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.BlockMaskLayout.rowMask rows ⟨j, hj⟩ : ℕ) ?_ ?_ ?_
         on_goal -1 =>
           first
           | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hprod, hprodInt, hmread]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [hprod, hprodInt, hmread] <;>
                 first
                 | omega
                 | (ring_nf; omega))
         on_goal -1 =>
           ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
             (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
             simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hprod, hprodInt, hmread] <;> omega)
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
         refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + j) (_root_.ThreeSum.BlockMaskLayout.rowMask rows ⟨j, hj⟩ : ℕ) ?_ ?_ ?_
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
      (focus
         ((first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
           repeat
             with_unfolding_none
               first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
         refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.BlockMaskLayout.prefixMask rows (j + 1) : ℕ) ?_ ?_ ?_
         on_goal -1 =>
           first
           | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hsum]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [hsum] <;>
                 first
                 | omega
                 | (ring_nf; omega))
         on_goal -1 =>
           ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
             (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
             simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsum] <;> omega)
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
         refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (2 ^ ((j + 1) * L) : ℕ) ?_ ?_ ?_
         on_goal -1 =>
           first
           | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hfactor, hfactorInt, hnextFactorInt]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [hfactor, hfactorInt, hnextFactorInt] <;>
                 first
                 | omega
                 | (ring_nf; omega))
         on_goal -1 =>
           ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
             (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
             simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hfactor, hfactorInt, hnextFactorInt] <;> omega)
         try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
      refine ⟨by simp,_root_.ThreeSum.BlockMaskLayout.rowMask rows ⟨j,hj⟩,
        Function.update μ' (dst+j) (_root_.ThreeSum.BlockMaskLayout.rowMask rows ⟨j,hj⟩ : ℤ),?_,?_,?_,?_⟩
      · simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]
      · have hlen : ((_root_.ThreeSum.BlockMaskLayout.packedMasks rows).take j).length = j := by simp; omega
        rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout.packedMasks_take_succ rows hj]
        simpa only [hlen] using _root_.ThreeSum1960614.Machine.Light.SegN.snoc hseg (_root_.ThreeSum.BlockMaskLayout.rowMask rows ⟨j,hj⟩)
      · intro i hi
        change Function.update μ' (dst+j) (_root_.ThreeSum.BlockMaskLayout.rowMask rows ⟨j,hj⟩ : ℤ) (work+i) = _
        rw [Function.update_of_ne (by omega)]
        exact hpowers' i hi
      · intro i hi
        change Function.update μ' (dst+j) (_root_.ThreeSum.BlockMaskLayout.rowMask rows ⟨j,hj⟩ : ℤ) i = _
        rw [Function.update_of_ne (by omega)]
        exact hkeep i hi
    case done =>
      intro σ _ h
      exact h
    case bound =>
      rintro j _ hj _ ⟨r,μ',rfl,_,_,_⟩
      (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
    case after =>
      rintro _ ⟨r,μ',rfl,hseg,hpowers',hkeep⟩
      have hb := hprefix J
      (focus
         ((first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
           repeat
             with_unfolding_none
               first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
         refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndex.indexSet (_root_.ThreeSum.BlockRows.flat rows)) : ℕ) ?_ ?_ ?_
         on_goal -1 =>
           first
           | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout.prefixMask_all]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [_root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout.prefixMask_all] <;>
                 first
                 | omega
                 | (ring_nf; omega))
         on_goal -1 =>
           ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
             (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
             simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout.prefixMask_all] <;> omega)
         try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
      have hfull : (_root_.ThreeSum.BlockMaskLayout.packedMasks rows).take J = _root_.ThreeSum.BlockMaskLayout.packedMasks rows := by
        simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout.packedMasks_length] using (List.take_length (l := _root_.ThreeSum.BlockMaskLayout.packedMasks rows))
      exact ⟨by simp,hfull ▸ hseg,hkeep⟩
  · have hJ : J = 0 := by omega
    subst J
    have hmask : _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndex.indexSet (_root_.ThreeSum.BlockRows.flat rows)) = 0 := by
      rw [← _root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout.prefixMask_all]
      exact _root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout.prefixMask_zero rows
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
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.Light.powTableTime]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.Light.powTableTime] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.Light.powTableTime] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    exact ⟨by simp [hmask],by simp [_root_.ThreeSum.BlockMaskLayout.packedMasks,_root_.ThreeSum1960614.Machine.Light.SegN],_root_.ThreeSum1960614.Machine.Light.SameOn.refl⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightBlockMasks.meets__implementation_e08124e141) := (@ThreeSum1960614.Machine.ThreeSum.LightBlockMasks.meets__implementation_e08124e141)

#print axioms solution
