-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSum.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:21:59.040026+00:00
-- url     : https://prove2.me/submissions/5a29e2e3-95a9-4981-842b-7b963da52fad

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
import Definitions.Def_ThreeSum1960614_Machine_Bundle025
import Definitions.Def_ThreeSum1960614_Machine_Bundle026
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
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
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
import Mathlib.Data.Finset.Max
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
import Mathlib.Data.List.Sublists
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSignedLeafGeneral_meets
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_union_sdiff
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_abs_le

namespace Finset
end Finset
namespace Light
end Light
namespace List
end List
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingSuffixCell
end ThreeSum.LightReportingSuffixCell
namespace ThreeSum.LightReportingSuffixSum
end ThreeSum.LightReportingSuffixSum
namespace ThreeSum.LightSignedLeafBatch
end ThreeSum.LightSignedLeafBatch
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.MaskDifference
end ThreeSum.MaskDifference
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.SignedLeaf
end ThreeSum.SignedLeaf
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.List
end ThreeSum1960614.Machine.List
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockForced
end ThreeSum1960614.Machine.ThreeSum.BlockForced
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCell
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCell
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSum
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSum
namespace ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch
end ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaCell
end ThreeSum1960614.Machine.ThreeSum.LightZetaCell
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.MaskDecode
end ThreeSum1960614.Machine.ThreeSum.MaskDecode
namespace ThreeSum1960614.Machine.ThreeSum.MaskDifference
end ThreeSum1960614.Machine.ThreeSum.MaskDifference
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
namespace ThreeSum1960614.Machine.ThreeSum.SignedLeaf
end ThreeSum1960614.Machine.ThreeSum.SignedLeaf
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

namespace ThreeSum1960614.Machine

/-!
# Compact addresses for bounded-cardinality bit masks

Both ranking and enumeration recurse on the highest available bit. The
enumerator stops immediately when the requested layer is empty. In
particular, it does not enumerate the ambient Boolean cube and filter it.
-/

namespace ThreeSum.SubsetAddress
open _root_.ThreeSum.SubsetAddress


set_option maxRecDepth 4000

open _root_.Finset
open scoped _root_.BigOperators

















































theorem layerOffset_succ (L k : ℕ) :
    _root_.ThreeSum.SubsetAddress.layerOffset L (k + 1) = _root_.ThreeSum.SubsetAddress.layerOffset L k + L.choose k := by
  exact Finset.sum_range_succ _ _

theorem layerOffset_mono (L : ℕ) : Monotone (_root_.ThreeSum.SubsetAddress.layerOffset L) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ]
  omega





theorem downsetRank_lt {L cut m : ℕ} (hm : m < 2 ^ L) (hk : _root_.ThreeSum.SubsetAddress.weight L m ≤ cut) :
    _root_.ThreeSum.SubsetAddress.downsetRank L m < _root_.ThreeSum.SubsetAddress.downsetCap L cut := by
  have hmask : _root_.ThreeSum.SubsetAddress.IsMask L (_root_.ThreeSum.SubsetAddress.weight L m) m := ⟨hm, rfl⟩
  have hr := _root_.ThreeSum.SubsetAddress.layerRank_lt hmask
  unfold _root_.ThreeSum.SubsetAddress.downsetRank _root_.ThreeSum.SubsetAddress.downsetCap
  calc
    _ < _root_.ThreeSum.SubsetAddress.layerOffset L (_root_.ThreeSum.SubsetAddress.weight L m) + L.choose (_root_.ThreeSum.SubsetAddress.weight L m) := Nat.add_lt_add_left hr _
    _ = _root_.ThreeSum.SubsetAddress.layerOffset L (_root_.ThreeSum.SubsetAddress.weight L m + 1) := (_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ L _).symm
    _ ≤ _ := _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_mono L (Nat.succ_le_succ (le_min hk hmask.le_width))





















































theorem subsetRank_lt {L cut : ℕ} {s : Finset (Fin L)} (hs : s.card ≤ cut) :
    _root_.ThreeSum.SubsetAddress.subsetRank s < _root_.ThreeSum.SubsetAddress.downsetCap L cut := by
  have hm := _root_.ThreeSum.SubsetAddress.subsetMask_isMask s
  exact _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.downsetRank_lt hm.1 (hm.2.trans_le hs)











end ThreeSum.SubsetAddress

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

theorem SameOn.trans (h₁ : _root_.ThreeSum1960614.Machine.Light.SameOn K μ μ') (h₂ : _root_.ThreeSum1960614.Machine.Light.SameOn K μ' μ'') : _root_.ThreeSum1960614.Machine.Light.SameOn K μ μ'' :=
  fun b hb => (h₂ b hb).trans (h₁ b hb)







/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}















/-! ## The tactics -/











end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Lists: entries with a default, blocks, sums, counting, sorted lists

General facts about lists. Arrays are lists here, and entry `i` of a list is `l.getD i d`. The
sections:

* Entries with a default: `getD` of a list that was appended to, cut, tabulated, mapped or changed
  in one place.
* Blocks: `(List.range n).flatMap f` puts the blocks `f 0, …, f (n - 1)` one after the other. Where
  an entry of a block stands, for blocks of any lengths and for blocks of one length.
* Sums: partial sums, the triangle inequality, and the sum over a list that enumerates the image of
  a finite set.
* A running minimum.
* Counting: how often a value occurs among the first entries of a list, or among the values of a
  function on `Fin n`; the list of the `j < n` with a property.
* Sorted lists: what `dropWhile` and `takeWhile` leave of a strictly increasing list; first
  occurrences in a weakly increasing list.
* Two notions of this project: `AbsLe l U` says that all members of `l` have absolute value at most
  `U`, and `sumLists` is the entrywise sum of lists of one length.
-/

@[expose] public section

namespace List
open _root_.List


variable {α β : Type*}

/-! ## Entries with a default -/



















/-! ## Blocks one after the other -/

















/-! ## Sums -/













section

variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]

/-- The triangle inequality for the sum of a list. -/
theorem abs_sum_le_sum_abs (l : List R) : |l.sum| ≤ (l.map fun x => |x|).sum :=
  Multiset.abs_sum_le_sum_abs (s := (l : Multiset R))

/-- The sum of an initial part of a list is at most the sum of the absolute values of the whole
list, in absolute value. -/
theorem abs_sum_take_le_sum_abs (l : List R) (k : ℕ) :
    |(l.take k).sum| ≤ (l.map fun x => |x|).sum := by
  refine (_root_.ThreeSum1960614.Machine.List.abs_sum_le_sum_abs _).trans ?_
  refine Sublist.sum_le_sum ((take_sublist k l).map _) fun a ha => ?_
  obtain ⟨x, -, rfl⟩ := mem_map.mp ha
  exact abs_nonneg x

end

/-- If `|f x| ≤ B` for all `x ∈ l`, then every initial part of the numbers `f x` has a sum of
absolute value at most `l.length * B`. -/
theorem abs_sum_take_map_le (l : List α) (f : α → ℤ) {B : ℤ} (h : ∀ x ∈ l, |f x| ≤ B) (k : ℕ) :
    |((l.map f).take k).sum| ≤ l.length * B := by
  refine (_root_.ThreeSum1960614.Machine.List.abs_sum_take_le_sum_abs _ k).trans ?_
  simpa using List.sum_le_card_nsmul ((l.map f).map fun x => |x|) B (by simpa using h)







/-! ## A running minimum -/





/-! ## Counting -/

















/-! ## Sorted lists -/

section Sorted

variable [LinearOrder α]







end Sorted

end List

namespace ThreeSumApsp
open _root_.ThreeSumApsp


variable {α β : Type*}

/-! ## Lists of integers that are bounded in absolute value -/









/-! ## The entrywise sum of lists -/





end ThreeSumApsp

end

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









theorem subsetMask_sdiff_int {L : ℕ} (Q U : Finset (Fin L)) (hU : U ⊆ Q) :
    (_root_.ThreeSum.SubsetAddress.subsetMask Q : ℤ)-(_root_.ThreeSum.SubsetAddress.subsetMask U : ℤ) = (_root_.ThreeSum.SubsetAddress.subsetMask (Q \ U) : ℤ) := by
  have h := _root_.ThreeSum.MaskDifference.subsetMask_union_sdiff Q U hU
  have hz : (_root_.ThreeSum.SubsetAddress.subsetMask U : ℤ)+(_root_.ThreeSum.SubsetAddress.subsetMask (Q \ U) : ℤ) = (_root_.ThreeSum.SubsetAddress.subsetMask Q : ℤ) := by
    exact_mod_cast h
  omega

end ThreeSum.MaskDifference

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





















































/-- Reading a cell of a segment of natural numbers, with the proof that the index is in range. -/
theorem SegN.getElem {l : List ℕ} (h : _root_.ThreeSum1960614.Machine.Light.SegN μ a l) {i : ℕ} (hi : i < l.length) :
    μ (a + i) = (l[i] : ℕ) := by
  rw [h i (by simpa using hi), List.getElem_map]

























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
# Signed leaf weights and the explicit part of sparse queries

The alternating sign is separated from the query cardinality, allowing
the same leaf weights to be used in stored boxes and direct leaf reads.
-/

namespace ThreeSum.SignedLeaf
open _root_.ThreeSum.SignedLeaf


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open scoped _root_.BigOperators





theorem abs_value_le {W cut B C : ℕ} (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (preL preR S : Finset (Fin W))
    (hstage : stage ≤ W) (hL : (preL ∪ S).card ≤ cut) (hR : (preR ∪ S).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ C) :
    |_root_.ThreeSum.SignedLeaf.value f g stage preL preR S| ≤ (((2^stage*B)*(2^stage*C) : ℕ) : ℤ) := by
  rw [_root_.ThreeSum.SignedLeaf.value,abs_mul,abs_neg_one_pow,one_mul,abs_mul]
  have h₁ := _root_.ThreeSum.SubsetStages.stageValue_abs_le f hf stage hstage (preL ∪ S) hL
  have h₂ := _root_.ThreeSum.SubsetStages.stageValue_abs_le g hg stage hstage (preR ∪ S) hR
  simpa only [Nat.cast_mul] using mul_le_mul h₁ h₂ (abs_nonneg _) (Int.natCast_nonneg _)

















end ThreeSum.SignedLeaf

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Initial signed-product table writes on one actual mask layer -/

namespace ThreeSum.LightSignedLeafBatch
open _root_.ThreeSum.LightSignedLeafBatch


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightZetaCell
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell
open _root_.ThreeSum.MaskDecode
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskDecode

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem storedThrough_of_on {W cut base : ℕ} {μ μ' : ℕ → ℤ}
    {f : Finset (Fin W) → ℤ}
    (h : _root_.ThreeSum.LightZetaStages.StoredThrough μ base cut f W)
    (hkeep : ∀ i, base ≤ i → i < base+(W+1)*_root_.ThreeSum.SubsetAddress.downsetCap W cut → μ' i = μ i) :
    _root_.ThreeSum.LightZetaStages.StoredThrough μ' base cut f W := by
  intro j hj S hS
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.subsetRank_lt hS
  have hm := Nat.mul_le_mul_right (_root_.ThreeSum.SubsetAddress.downsetCap W cut) (Nat.succ_le_succ hj)
  simp only [Nat.succ_mul] at hm
  have he := hkeep (base+j*_root_.ThreeSum.SubsetAddress.downsetCap W cut+_root_.ThreeSum.SubsetAddress.subsetRank S) (by omega) (by
    simp only [Nat.succ_mul]
    omega)
  exact he.trans (h j hj S hS)















end ThreeSum.LightSignedLeafBatch

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Local suffix coordinates with exact global source semantics

The remaining ambient ground set has width V, whereas source transforms use
the original width W. A contiguous shift embeds local box masks into global
source masks. Enumeration and box-table addresses can therefore use V without
changing the original raw-incidence query.
-/

namespace ThreeSum.ReportingHostSuffix
open _root_.ThreeSum.ReportingHostSuffix


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open scoped _root_.BigOperators



@[simp] theorem shiftEmbedding_val {W V offset : ℕ} (hfit : offset+V ≤ W) (i : Fin V) :
    (_root_.ThreeSum.ReportingHostSuffix.shiftEmbedding offset hfit i).val = offset+i.val := rfl



@[simp] theorem liftSet_card {W V offset : ℕ} (hfit : offset+V ≤ W) (S : Finset (Fin V)) :
    (_root_.ThreeSum.ReportingHostSuffix.liftSet hfit S).card = S.card := Finset.card_map _





theorem liftSet_subset {W V offset : ℕ} (hfit : offset+V ≤ W) (S T : Finset (Fin V)) :
    _root_.ThreeSum.ReportingHostSuffix.liftSet hfit S ⊆ _root_.ThreeSum.ReportingHostSuffix.liftSet hfit T ↔ S ⊆ T := Finset.map_subset_map

theorem liftSet_mask {W V offset : ℕ} (hfit : offset+V ≤ W) (S : Finset (Fin V)) :
    _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.ReportingHostSuffix.liftSet hfit S) = 2^offset*_root_.ThreeSum.SubsetAddress.subsetMask S := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.MaskDifference.subsetMask_sum,_root_.ThreeSum.ReportingHostSuffix.liftSet,Finset.sum_map,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix.shiftEmbedding_val,
    pow_add,Finset.mul_sum]

theorem liftSet_mask_int {W V offset : ℕ} (hfit : offset+V ≤ W) (S : Finset (Fin V)) :
    (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.ReportingHostSuffix.liftSet hfit S) : ℤ) = (2^offset : ℕ)*(_root_.ThreeSum.SubsetAddress.subsetMask S : ℤ) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix.liftSet_mask]
  push_cast
  rfl













theorem leafWeight_abs_le {W V offset sourceCut stage B D : ℕ} (hfit : offset+V ≤ W)
    (f g : Finset (Fin W) → ℤ) (preL preR : Finset (Fin W)) (S : Finset (Fin V))
    (hstage : stage ≤ W) (hL : (preL ∪ _root_.ThreeSum.ReportingHostSuffix.liftSet hfit S).card ≤ sourceCut)
    (hR : (preR ∪ _root_.ThreeSum.ReportingHostSuffix.liftSet hfit S).card ≤ sourceCut)
    (hf : ∀ T, T.card ≤ sourceCut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ sourceCut → |g T| ≤ D) :
    |_root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage preL preR S| ≤ (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SignedLeaf.abs_value_le f g stage preL preR _ hstage hL hR hf hg













section Original

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts



end Original
end ThreeSum.ReportingHostSuffix

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A concrete box-leaf cell with global source and local box addresses

Multiplication lifts the local mask into the global suffix. The actual source
reader uses width W; a second actual compact-address computation uses width V.
Only the local compact box cell and polynomial scratch are modified.
-/

namespace ThreeSum.LightReportingSuffixCell
open _root_.ThreeSum.LightReportingSuffixCell


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.LightZetaCell
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}





theorem small_word {W V : ℕ} (hV : V ≤ W)
    (hw : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word) :
    (((V+1)*2^(V+1) : ℕ) : ℤ) ≤ lim.word := by
  have hm := Nat.mul_le_mul (Nat.succ_le_succ hV)
    (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (Nat.succ_le_succ hV))
  exact (by exact_mod_cast hm : (((V+1)*2^(V+1) : ℕ) : ℤ) ≤
    (((W+1)*2^(W+1) : ℕ) : ℤ)).trans hw











end ThreeSum.LightReportingSuffixCell

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Explicit local suffix leaves evaluated by actual global source reads -/

namespace ThreeSum.LightReportingSuffixSum
open _root_.ThreeSum.LightReportingSuffixSum


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}





theorem partialSum_succ {W V offset : ℕ} (hfit : offset+V ≤ W) (Q : Finset (Fin V))
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (missing : List (Finset (Fin V))) {j : ℕ} (hj : j < missing.length) :
    _root_.ThreeSum.LightReportingSuffixSum.partialSum hfit Q preL preR f g stage missing (j+1) =
      _root_.ThreeSum.LightReportingSuffixSum.partialSum hfit Q preL preR f g stage missing j+_root_.ThreeSum.LightReportingSuffixSum.term hfit Q preL preR f g stage missing[j] := by
  unfold _root_.ThreeSum.LightReportingSuffixSum.partialSum
  rw [List.sum_take_succ _ _ (by simpa using hj),List.getElem_map]

@[simp] theorem partialSum_length {W V offset : ℕ} (hfit : offset+V ≤ W) (Q : Finset (Fin V))
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (missing : List (Finset (Fin V))) :
    _root_.ThreeSum.LightReportingSuffixSum.partialSum hfit Q preL preR f g stage missing missing.length =
      (missing.map (_root_.ThreeSum.LightReportingSuffixSum.term hfit Q preL preR f g stage)).sum := by
  unfold _root_.ThreeSum.LightReportingSuffixSum.partialSum
  have he : missing.length = (missing.map (_root_.ThreeSum.LightReportingSuffixSum.term hfit Q preL preR f g stage)).length :=
    (List.length_map _).symm
  rw [he,List.take_length]













end ThreeSum.LightReportingSuffixSum

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightReportingSuffixSum
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSum

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSum.meets__implementation_d2eb52a77c {pMain pLeaf pAddress : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSum.body pLeaf)) (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafCell.Procs P pLeaf pAddress)
    {μ : ℕ → ℤ} {W V offset cut stage t maskBase baseL baseR work B D d : ℕ}
    (hfit : offset+V ≤ W) (Q : Finset (Fin V)) (preL preR : Finset (Fin W))
    (missing : List (Finset (Fin V))) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*_root_.ThreeSum.SubsetAddress.downsetCap W cut ≤ work)
    (hdataR : baseR+(W+1)*_root_.ThreeSum.SubsetAddress.downsetCap W cut ≤ work)
    (hmasks : maskBase+missing.length ≤ work)
    (hspace : work+1+_root_.ThreeSum.LightPascal.tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hproductWord : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤ lim.word)
    (haccWord : ((missing.length*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word)
    (hcardL : (preL ∪ _root_.ThreeSum.ReportingHostSuffix.liftSet hfit Q).card ≤ cut)
    (hcardR : (preR ∪ _root_.ThreeSum.ReportingHostSuffix.liftSet hfit Q).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ D)
    (hvalid : ∀ U ∈ missing, U ⊆ Q ∧ U.card = t)
    (hstoredL : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseR cut g W)
    (hseg : _root_.ThreeSum1960614.Machine.Light.SegN μ maskBase (missing.map _root_.ThreeSum.SubsetAddress.subsetMask))
    (hd : d+W+7 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d
      [W,cut,stage,preL.card,_root_.ThreeSum.SubsetAddress.subsetMask preL,preR.card,_root_.ThreeSum.SubsetAddress.subsetMask preR,V,2^offset,
        Q.card,_root_.ThreeSum.SubsetAddress.subsetMask Q,t,missing.length,maskBase,baseL,baseR,work] μ (_root_.ThreeSum.LightReportingSuffixSum.time W missing.length)
      (fun r μ' => r = (missing.map (_root_.ThreeSum.LightReportingSuffixSum.term hfit Q preL preR f g stage)).sum ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ μ' work) := by
  have hQcard : Q.card ≤ V := by simpa using Finset.card_le_univ Q
  have hMaskWord (S : Finset (Fin W)) : (_root_.ThreeSum.SubsetAddress.subsetMask S : ℤ) ≤ lim.word := by
    have hp : _root_.ThreeSum.SubsetAddress.subsetMask S ≤ (W+1)*2^(W+1) :=
      (Nat.le_of_lt (_root_.ThreeSum.SubsetAddress.subsetMask_isMask S).1).trans
        ((Nat.pow_le_pow_right (by decide) (by omega)).trans (Nat.le_mul_of_pos_left _ (by omega)))
    exact (by exact_mod_cast hp : (subsetMask S : ℤ) ≤ (((W+1)*2^(W+1) : ℕ) : ℤ)).trans hword
  have hLocalMaskWord (S : Finset (Fin V)) : (_root_.ThreeSum.SubsetAddress.subsetMask S : ℤ) ≤ lim.word := by
    have hp : _root_.ThreeSum.SubsetAddress.subsetMask S ≤ (V+1)*2^(V+1) :=
      (Nat.le_of_lt (_root_.ThreeSum.SubsetAddress.subsetMask_isMask S).1).trans
        ((Nat.pow_le_pow_right (by decide) (by omega)).trans (Nat.le_mul_of_pos_left _ (by omega)))
    exact (by exact_mod_cast hp : (subsetMask S : ℤ) ≤ (((V+1)*2^(V+1) : ℕ) : ℤ)).trans
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCell.small_word (by omega : V ≤ W) hword)
  have hQmask := hLocalMaskWord Q
  have hflagsL (U : Finset (Fin V)) : (preL ∪ _root_.ThreeSum.ReportingHostSuffix.liftSet hfit (Q \ U)).card ≤ cut :=
    (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl preL)
      ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix.liftSet_subset hfit _ _).mpr Finset.sdiff_subset))).trans hcardL
  have hflagsR (U : Finset (Fin V)) : (preR ∪ _root_.ThreeSum.ReportingHostSuffix.liftSet hfit (Q \ U)).card ≤ cut :=
    (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl preR)
      ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix.liftSet_subset hfit _ _).mpr Finset.sdiff_subset))).trans hcardR
  have htermBound : ∀ U ∈ missing, |_root_.ThreeSum.LightReportingSuffixSum.term hfit Q preL preR f g stage U| ≤
      (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) := by
    intro U _
    exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix.leafWeight_abs_le hfit f g preL preR _ hstage (hflagsL U) (hflagsR U) hf hg
  have hacc (j : ℕ) : |_root_.ThreeSum.LightReportingSuffixSum.partialSum hfit Q preL preR f g stage missing j| ≤ lim.word := by
    have hh := _root_.ThreeSum1960614.Machine.List.abs_sum_take_map_le missing (_root_.ThreeSum.LightReportingSuffixSum.term hfit Q preL preR f g stage) htermBound j
    exact hh.trans (by simpa only [Nat.cast_mul] using haccWord)
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSum.body _root_.ThreeSum.LightReportingSuffixSum.time
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
    (T := missing.length*(_root_.ThreeSum.LightSignedLeafGeneral.time W+90)+20)
    (Q := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSum.Inv hfit μ Q preL preR f g stage missing cut t maskBase baseL baseR work missing.length)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSum.Inv hfit μ Q preL preR f g stage missing cut t maskBase baseL baseR work)
    missing.length (_root_.ThreeSum.LightSignedLeafGeneral.time W+80) ?start ?round ?done ?bound (hT := by (first
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
    refine ⟨0,0,μ,?_,_root_.ThreeSum1960614.Machine.Light.SameOn.refl⟩
    simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal,_root_.ThreeSum.LightReportingSuffixSum.partialSum]
    change _root_.Light.frame [(W : ℤ),cut,stage,preL.card,_root_.ThreeSum.SubsetAddress.subsetMask preL,preR.card,_root_.ThreeSum.SubsetAddress.subsetMask preR,
      V,2^offset,Q.card,_root_.ThreeSum.SubsetAddress.subsetMask Q,t,missing.length,maskBase,baseL,baseR,work,0,0] =
      _root_.Light.frame ([(W : ℤ),cut,stage,preL.card,_root_.ThreeSum.SubsetAddress.subsetMask preL,preR.card,_root_.ThreeSum.SubsetAddress.subsetMask preR,
      V,2^offset,Q.card,_root_.ThreeSum.SubsetAddress.subsetMask Q,t,missing.length,maskBase,baseL,baseR,work,0,0] ++ [0,0])
    exact (_root_.ThreeSum1960614.Machine.Light.frame_append_zeros _ 2).symm
  case round =>
    rintro j _ hj _ ⟨mask,r,μ',rfl,hkeep⟩
    let U := missing[j]
    have hu := hvalid U (List.getElem_mem hj)
    have hstoredL' := _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch.storedThrough_of_on hstoredL
      (by intro i _ hi; exact hkeep i (hi.trans_le hdataL))
    have hstoredR' := _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch.storedThrough_of_on hstoredR
      (by intro i _ hi; exact hkeep i (hi.trans_le hdataR))
    have hmask : μ' (maskBase+j) = (_root_.ThreeSum.SubsetAddress.subsetMask U : ℤ) := by
      have hr := hseg.getElem (by simpa using hj)
      simp only [List.getElem_map] at hr
      exact (hkeep _ (by omega)).trans hr
    have hcard : (Q \ U).card = Q.card-t := by rw [Finset.card_sdiff_of_subset hu.1,hu.2]
    have hmaskSub := _root_.ThreeSum1960614.Machine.ThreeSum.MaskDifference.subsetMask_sdiff_int Q U hu.1
    have hcardInt : (Q.card : ℤ)-(t : ℤ) = ((Q \ U).card : ℤ) := by
      rw [hcard,Int.ofNat_sub (by rw [← hu.2]; exact Finset.card_le_card hu.1)]
    have hscaled : ((_root_.ThreeSum.SubsetAddress.subsetMask Q : ℤ)-(_root_.ThreeSum.SubsetAddress.subsetMask U : ℤ))*(2 : ℤ)^offset =
        (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.ReportingHostSuffix.liftSet hfit (Q \ U)) : ℤ) := by
      rw [hmaskSub,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix.liftSet_mask_int]
      push_cast
      ring
    have hlocalWord := hLocalMaskWord (Q \ U)
    have hScaledBounds : -lim.word ≤
        ((_root_.ThreeSum.SubsetAddress.subsetMask Q : ℤ)-(_root_.ThreeSum.SubsetAddress.subsetMask U : ℤ))*(2 : ℤ)^offset ∧
        ((_root_.ThreeSum.SubsetAddress.subsetMask Q : ℤ)-(_root_.ThreeSum.SubsetAddress.subsetMask U : ℤ))*(2 : ℤ)^offset ≤ lim.word := by
      rw [hscaled]
      have := hMaskWord (_root_.ThreeSum.ReportingHostSuffix.liftSet hfit (Q \ U))
      have := Int.natCast_nonneg (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.ReportingHostSuffix.liftSet hfit (Q \ U)))
      omega
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSum.roundBody
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.ReportingHostSuffix.liftSet hfit (Q \ U)) : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hmask, hscaled, _root_.ThreeSum.LightSignedLeafGeneral.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hmask, hscaled, _root_.ThreeSum.LightSignedLeafGeneral.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hmask, hscaled, _root_.ThreeSum.LightSignedLeafGeneral.time] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    have hc := _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafGeneral.meets (d := d+1)
      C.leaf C.union C.lookup C.sign C.size C.address C.setup C.offset C.erase
      preL preR (_root_.ThreeSum.ReportingHostSuffix.liftSet hfit (Q \ U)) f g hw hcut hstage hdataL hdataR hspace hword hproductWord
      (hflagsL U) (hflagsR U) hf hg hstoredL' hstoredR' (by omega)
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix.liftSet_card] at hc
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
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcardInt, _root_.ThreeSum.LightSignedLeafGeneral.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hcardInt, _root_.ThreeSum.LightSignedLeafGeneral.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcardInt, _root_.ThreeSum.LightSignedLeafGeneral.time] <;> omega)
       on_goal -1 => (rintro res μ₁ ⟨hres, hnewKeep⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    have hnext := abs_le.mp (hacc (j+1))
    have hsum : _root_.ThreeSum.LightReportingSuffixSum.partialSum hfit Q preL preR f g stage missing j+_root_.ThreeSum.LightReportingSuffixSum.term hfit Q preL preR f g stage U =
        _root_.ThreeSum.LightReportingSuffixSum.partialSum hfit Q preL preR f g stage missing (j+1) :=
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSum.partialSum_succ hfit Q preL preR f g stage missing hj).symm
    have hres' : res = _root_.ThreeSum.LightReportingSuffixSum.term hfit Q preL preR f g stage U := hres
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightReportingSuffixSum.partialSum hfit Q preL preR f g stage missing (j + 1)) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hres', hsum, _root_.ThreeSum.LightSignedLeafGeneral.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hres', hsum, _root_.ThreeSum.LightSignedLeafGeneral.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hres', hsum, _root_.ThreeSum.LightSignedLeafGeneral.time] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    refine ⟨by simp,(_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.ReportingHostSuffix.liftSet hfit (Q \ U)) : ℤ),res,μ₁,?_,hkeep.trans hnewKeep⟩
    simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]
  case done =>
    intro σ _ h
    exact h
  case bound =>
    rintro j _ hj _ ⟨mask,r,μ',rfl,_⟩
    (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
  case after =>
    rintro _ ⟨mask,r,μ',rfl,hkeep⟩
    have ha := abs_le.mp (hacc missing.length)
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen ((missing.map (_root_.ThreeSum.LightReportingSuffixSum.term hfit Q preL preR f g stage)).sum) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSum.partialSum_length]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSum.partialSum_length] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSum.partialSum_length] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    exact ⟨by simp,hkeep⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSum.meets__implementation_d2eb52a77c) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSum.meets__implementation_d2eb52a77c)

#print axioms solution
