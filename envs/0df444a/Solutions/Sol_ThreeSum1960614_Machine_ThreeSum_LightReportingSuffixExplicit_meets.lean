-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixExplicit.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:27:21.527995+00:00
-- url     : https://prove2.me/submissions/ad59e29d-d571-4126-93e4-a98acc318a1c

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightQueryEnumeration_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingSuffixSum_meets
import Theorems.Thm_ThreeSum_SubsetAddress_enumerationWork_bound
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
namespace ThreeSum.ExplicitLayers
end ThreeSum.ExplicitLayers
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightDownsetAddress
end ThreeSum.LightDownsetAddress
namespace ThreeSum.LightDownsetSize
end ThreeSum.LightDownsetSize
namespace ThreeSum.LightMaskUnion
end ThreeSum.LightMaskUnion
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightQueryEnumeration
end ThreeSum.LightQueryEnumeration
namespace ThreeSum.LightQueryWeights
end ThreeSum.LightQueryWeights
namespace ThreeSum.LightReportingSuffixExplicit
end ThreeSum.LightReportingSuffixExplicit
namespace ThreeSum.LightReportingSuffixSum
end ThreeSum.LightReportingSuffixSum
namespace ThreeSum.LightSignedLeafBatch
end ThreeSum.LightSignedLeafBatch
namespace ThreeSum.LightSignedLeafGeneral
end ThreeSum.LightSignedLeafGeneral
namespace ThreeSum.LightStageLookup
end ThreeSum.LightStageLookup
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightSubsetEnumeration
end ThreeSum.LightSubsetEnumeration
namespace ThreeSum.LightSubsetSetup
end ThreeSum.LightSubsetSetup
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.MaskUnion
end ThreeSum.MaskUnion
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
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
namespace ThreeSum1960614.Machine.ThreeSum.ExplicitLayers
end ThreeSum1960614.Machine.ThreeSum.ExplicitLayers
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightDownsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightDownsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightDownsetSize
end ThreeSum1960614.Machine.ThreeSum.LightDownsetSize
namespace ThreeSum1960614.Machine.ThreeSum.LightMaskUnion
end ThreeSum1960614.Machine.ThreeSum.LightMaskUnion
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration
end ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightQueryWeights
end ThreeSum1960614.Machine.ThreeSum.LightQueryWeights
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixExplicit
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixExplicit
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSum
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSum
namespace ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch
end ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch
namespace ThreeSum1960614.Machine.ThreeSum.LightSignedLeafGeneral
end ThreeSum1960614.Machine.ThreeSum.LightSignedLeafGeneral
namespace ThreeSum1960614.Machine.ThreeSum.LightStageLookup
end ThreeSum1960614.Machine.ThreeSum.LightStageLookup
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration
end ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup
end ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaCell
end ThreeSum1960614.Machine.ThreeSum.LightZetaCell
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.MaskDecode
end ThreeSum1960614.Machine.ThreeSum.MaskDecode
namespace ThreeSum1960614.Machine.ThreeSum.MaskErase
end ThreeSum1960614.Machine.ThreeSum.MaskErase
namespace ThreeSum1960614.Machine.ThreeSum.MaskUnion
end ThreeSum1960614.Machine.ThreeSum.MaskUnion
namespace ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
end ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
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
# A rectangular Pascal table in the benchmark language

Every coefficient is built once by addition from the preceding row.
The row-major representation supports one multiplication and two additions
per later lookup. No recursive binomial-coefficient evaluation is used.
-/

namespace ThreeSum.LightPascal
open _root_.ThreeSum.LightPascal


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



















theorem buildTime_bound (L : ℕ) : _root_.ThreeSum.LightPascal.buildTime L ≤ 1000*(L+1)^2 := by
  unfold _root_.ThreeSum.LightPascal.buildTime _root_.ThreeSum.LightPascal.rowTime _root_.ThreeSum.LightArray.linearTime
  simp only [_root_.Light.fillTime]
  nlinarith

end ThreeSum.LightPascal

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# General mask union and its cardinality on the bounded-word machine

The program tests each coordinate using the checked bit-deletion routine.
It constructs its own powers table, adds each new bit once, and writes the
union cardinality to one output cell. It never visits an ambient cube.
-/

namespace ThreeSum.LightMaskUnion
open _root_.ThreeSum.LightMaskUnion


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.MaskErase
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.MaskUnion
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskUnion

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}















theorem time_bound (W : ℕ) : _root_.ThreeSum.LightMaskUnion.time W ≤ 800*(W+1)^2 := by
  unfold _root_.ThreeSum.LightMaskUnion.time _root_.Light.powTableTime _root_.ThreeSum.LightMaskErase.time
  nlinarith

end ThreeSum.LightMaskUnion

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Output-sensitive subset-layer enumeration in the benchmark language

The recursive routine writes into consecutive output cells. Empty layers
return immediately; a zero-cardinality layer emits one mask. The two
recursive children share the output buffer and write adjacent, disjoint
segments. No ambient Boolean cube is scanned and no output list is copied.
-/

namespace ThreeSum.LightSubsetEnumeration
open _root_.ThreeSum.LightSubsetEnumeration


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

















theorem time_bound (L k : ℕ) :
    _root_.ThreeSum.LightSubsetEnumeration.time L k ≤ 150*((4*L+1)*L.choose k+1) := by
  exact Nat.mul_le_mul_left 150 (_root_.ThreeSum.SubsetAddress.enumerationWork_bound L k)







end ThreeSum.LightSubsetEnumeration

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A complete subset-rank program, including table construction

This fixed program constructs both lookup tables in scratch and then ranks
one valid mask. Its cost is quadratic in the bit width. The faster cached
rank contract remains available separately, but no supplied table correctness
assumption appears in the fixed-program result below.
-/

namespace ThreeSum.LightSubsetSetup
open _root_.ThreeSum.LightSubsetSetup


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}















theorem time_bound (L : ℕ) : _root_.ThreeSum.LightSubsetSetup.time L ≤ 1200*(L+1)^2 := by
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal.buildTime_bound L
  unfold _root_.ThreeSum.LightSubsetSetup.time _root_.Light.powTableTime _root_.ThreeSum.LightSubsetAddress.rankTime
  nlinarith

end ThreeSum.LightSubsetSetup

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A fixed program for the complete compact downset address

The input gives a mask and its known cardinality. The program constructs
its own Pascal and power tables, computes the layer rank, scans the layer
offset, and returns their sum. No table-correctness or algorithmic runtime
premise is supplied by the caller.
-/

namespace ThreeSum.LightDownsetAddress
open _root_.ThreeSum.LightDownsetAddress


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}













theorem time_bound (L : ℕ) : _root_.ThreeSum.LightDownsetAddress.time L ≤ 1300*(L+1)^2 := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup.time_bound L
  unfold _root_.ThreeSum.LightDownsetAddress.time _root_.ThreeSum.LightSubsetOffset.time
  nlinarith

end ThreeSum.LightDownsetAddress

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Computing the compact downset size

The program builds a Pascal table, scans all preceding layers, and adds
the final binomial coefficient. The table stride used by the transform
is therefore computed by an actual fixed program.
-/

namespace ThreeSum.LightDownsetSize
open _root_.ThreeSum.LightDownsetSize


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}















theorem time_bound (L : ℕ) : _root_.ThreeSum.LightDownsetSize.time L ≤ 1400*(L+1)^2 := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup.time_bound L
  have hp : 1 ≤ (L+1)^2 := Nat.one_le_pow' 2 L
  unfold _root_.ThreeSum.LightDownsetSize.time _root_.ThreeSum.LightSubsetOffset.time
  nlinarith

end ThreeSum.LightDownsetSize

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Query-coordinate lists and weighted subset semantics

The coordinate list has one entry per set bit of the query. Its powers
form a compact weight table for the output-sensitive enumeration routine.
-/

namespace ThreeSum.QueryCoordinates
open _root_.ThreeSum.QueryCoordinates


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open scoped _root_.BigOperators















@[simp] theorem positions_length {W : ℕ} (Q : Finset (Fin W)) :
    (_root_.ThreeSum.QueryCoordinates.positions Q W).length = Q.card := by
  rw [← List.toFinset_card_of_nodup (_root_.ThreeSum.QueryCoordinates.positions_nodup Q W),_root_.ThreeSum.QueryCoordinates.positions_toFinset,_root_.ThreeSum.SubsetAddress.natPositions_card]



















@[simp] theorem setLayer_length (xs : List ℕ) (k : ℕ) :
    (_root_.ThreeSum.QueryCoordinates.setLayer xs k).length = xs.length.choose k := by
  simp [_root_.ThreeSum.QueryCoordinates.setLayer,List.length_sublistsLen]























@[simp] theorem missingSets_length {W : ℕ} (Q : Finset (Fin W)) (k : ℕ) :
    (_root_.ThreeSum.QueryCoordinates.missingSets Q k).length = Q.card.choose k := by
  simp [_root_.ThreeSum.QueryCoordinates.missingSets]



end ThreeSum.QueryCoordinates

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Constructing the compact coordinate-weight table of a query mask

A width-sized scan tests each bit using the checked deletion routine and
appends the corresponding power of two. The output has one cell per set
bit, while the available buffer and scratch are only linear in the width.
-/

namespace ThreeSum.LightQueryWeights
open _root_.ThreeSum.LightQueryWeights


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.MaskErase
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

















theorem time_bound (W : ℕ) : _root_.ThreeSum.LightQueryWeights.time W ≤ 500*(W+1)^2 := by
  unfold _root_.ThreeSum.LightQueryWeights.time _root_.Light.powTableTime _root_.ThreeSum.LightMaskErase.time
  nlinarith

end ThreeSum.LightQueryWeights

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Executing a stored partial-zeta or box lookup

This fixed program computes the compact downset stride and the queried
subset rank from freshly built tables. It then reads exactly one stored
stage cell. The specialized contracts connect that machine read to the
forced-prefix sum and to the canonical sparse-box sum.
-/

namespace ThreeSum.LightStageLookup
open _root_.ThreeSum.LightStageLookup


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}



















theorem time_bound (L : ℕ) : _root_.ThreeSum.LightStageLookup.time L ≤ 2800*(L+1)^2 := by
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.time_bound L
  have ha := _root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetAddress.time_bound L
  have hp : 1 ≤ (L+1)^2 := Nat.one_le_pow' 2 L
  unfold _root_.ThreeSum.LightStageLookup.time
  omega

end ThreeSum.LightStageLookup

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









@[simp] theorem mem_explicitMissing {W : ℕ} (Q U : Finset (Fin W)) (t : ℕ) :
    U ∈ _root_.ThreeSum.SignedLeaf.explicitMissing Q t ↔ U ⊆ Q ∧ U.card < t := by
  simp only [_root_.ThreeSum.SignedLeaf.explicitMissing,List.mem_flatMap,List.mem_range,_root_.ThreeSum.QueryCoordinates.missingSets_mem]
  constructor
  · rintro ⟨j,hj,hU,hcard⟩
    exact ⟨hU,by omega⟩
  · rintro ⟨hU,ht⟩
    exact ⟨U.card,ht,hU,rfl⟩





theorem mem_explicitLeaves {W : ℕ} (Q S : Finset (Fin W)) (t : ℕ) :
    S ∈ _root_.ThreeSum.SignedLeaf.explicitLeaves Q t ↔ S ⊆ Q ∧ (Q \ S).card < t := by
  constructor
  · intro h
    obtain ⟨U,hU,rfl⟩ := List.mem_map.mp h
    have hu := (_root_.ThreeSum1960614.Machine.ThreeSum.SignedLeaf.mem_explicitMissing Q U t).mp hU
    exact ⟨Finset.sdiff_subset,by rw [Finset.sdiff_sdiff_eq_self hu.1]; exact hu.2⟩
  · rintro ⟨hS,ht⟩
    exact List.mem_map.mpr ⟨Q \ S,(_root_.ThreeSum1960614.Machine.ThreeSum.SignedLeaf.mem_explicitMissing Q _ t).mpr ⟨Finset.sdiff_subset,ht⟩,
      Finset.sdiff_sdiff_eq_self hS⟩

end ThreeSum.SignedLeaf

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact values and sizes of the explicitly evaluated missing layers -/

namespace ThreeSum.ExplicitLayers
open _root_.ThreeSum.ExplicitLayers


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open scoped _root_.BigOperators

@[simp] theorem missing_length {W : ℕ} (Q : Finset (Fin W)) (t : ℕ) :
    (_root_.ThreeSum.SignedLeaf.explicitMissing Q t).length = _root_.ThreeSum.SubsetAddress.layerOffset Q.card t := by
  unfold _root_.ThreeSum.SignedLeaf.explicitMissing
  rw [List.length_flatMap]
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.missingSets_length]
  have he := List.sum_toFinset (fun j => Q.card.choose j) (List.nodup_range (n := t))
  simpa only [List.toFinset_range,_root_.ThreeSum.SubsetAddress.layerOffset] using he.symm

@[simp] theorem leaves_length {W : ℕ} (Q : Finset (Fin W)) (t : ℕ) :
    (_root_.ThreeSum.SignedLeaf.explicitLeaves Q t).length = _root_.ThreeSum.SubsetAddress.layerOffset Q.card t := by
  simp [_root_.ThreeSum.SignedLeaf.explicitLeaves]

theorem choose_le_offset {c j t : ℕ} (hj : j < t) : c.choose j ≤ _root_.ThreeSum.SubsetAddress.layerOffset c t := by
  exact Finset.single_le_sum (fun i hi => Nat.zero_le (c.choose i)) (Finset.mem_range.mpr hj)



@[simp] theorem valueSum_zero {W : ℕ} (Q : Finset (Fin W)) (weight : Finset (Fin W) → ℤ) :
    _root_.ThreeSum.ExplicitLayers.valueSum Q weight 0 = 0 := by
  simp [_root_.ThreeSum.ExplicitLayers.valueSum,_root_.ThreeSum.SignedLeaf.explicitLeaves,_root_.ThreeSum.SignedLeaf.explicitMissing]

theorem valueSum_succ {W : ℕ} (Q : Finset (Fin W)) (weight : Finset (Fin W) → ℤ) (t : ℕ) :
    _root_.ThreeSum.ExplicitLayers.valueSum Q weight (t+1) = _root_.ThreeSum.ExplicitLayers.valueSum Q weight t+
      ((_root_.ThreeSum.QueryCoordinates.missingSets Q t).map fun U => weight (Q \ U)).sum := by
  simp [_root_.ThreeSum.ExplicitLayers.valueSum,_root_.ThreeSum.SignedLeaf.explicitLeaves,_root_.ThreeSum.SignedLeaf.explicitMissing,List.range_succ,
    List.flatMap_append,List.map_append,List.map_map,Function.comp_def,List.sum_append]

theorem valueSum_abs_le {W B : ℕ} (Q : Finset (Fin W)) (weight : Finset (Fin W) → ℤ) (t : ℕ)
    (hw : ∀ S, S ⊆ Q → |weight S| ≤ B) :
    |_root_.ThreeSum.ExplicitLayers.valueSum Q weight t| ≤ ((_root_.ThreeSum.SubsetAddress.layerOffset Q.card t*B : ℕ) : ℤ) := by
  have hh := _root_.ThreeSum1960614.Machine.List.abs_sum_take_map_le (_root_.ThreeSum.SignedLeaf.explicitLeaves Q t) weight
    (fun S hs => hw S ((_root_.ThreeSum1960614.Machine.ThreeSum.SignedLeaf.mem_explicitLeaves Q S t).mp hs).1)
    (_root_.ThreeSum.SignedLeaf.explicitLeaves Q t).length
  have he : (_root_.ThreeSum.SignedLeaf.explicitLeaves Q t).length =
      ((_root_.ThreeSum.SignedLeaf.explicitLeaves Q t).map weight).length := (List.length_map _).symm
  rw [he,List.take_length] at hh
  simpa only [_root_.ThreeSum.ExplicitLayers.valueSum,List.length_map,_root_.ThreeSum1960614.Machine.ThreeSum.ExplicitLayers.leaves_length,Nat.cast_mul] using hh





end ThreeSum.ExplicitLayers

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A complete output-sensitive subset enumerator inside an arbitrary query mask

The routine constructs its own compact coordinate weights, then invokes
the existing recursion on the number of selected coordinates. Every emitted
word is already a global mask; no ambient layer or Boolean cube is scanned.
-/

namespace ThreeSum.LightQueryEnumeration
open _root_.ThreeSum.LightQueryEnumeration


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}











theorem time_bound {W c t : ℕ} (hc : c ≤ W) :
    _root_.ThreeSum.LightQueryEnumeration.time W c t ≤ 1400*(W+1)^2*(c.choose t+1) := by
  have hbuild := _root_.ThreeSum1960614.Machine.ThreeSum.LightQueryWeights.time_bound W
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.time_bound c t
  unfold _root_.ThreeSum.LightQueryEnumeration.time
  have hpoly : (4*c+1)*c.choose t+1 ≤ 4*(W+1)^2*(c.choose t+1) := by
    have hW : W+1 ≤ (W+1)^2 := by nlinarith
    nlinarith
  nlinarith [Nat.one_le_pow' 2 W]

end ThreeSum.LightQueryEnumeration

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Signed leaves with arbitrary prefix overlap

Two bounded width scans construct the actual prefix unions and their
cardinalities. The compact source-table reads and signed multiplication
then give the same leaf function used by the sparse query theorem.
-/

namespace ThreeSum.LightSignedLeafGeneral
open _root_.ThreeSum.LightSignedLeafGeneral


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}













theorem time_bound (W : ℕ) : _root_.ThreeSum.LightSignedLeafGeneral.time W ≤ 7800*(W+1)^2 := by
  have hu := _root_.ThreeSum1960614.Machine.ThreeSum.LightMaskUnion.time_bound W
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.LightStageLookup.time_bound W
  unfold _root_.ThreeSum.LightSignedLeafGeneral.time _root_.ThreeSum.LightSign.time
  nlinarith

end ThreeSum.LightSignedLeafGeneral

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













theorem liftSet_subset {W V offset : ℕ} (hfit : offset+V ≤ W) (S T : Finset (Fin V)) :
    _root_.ThreeSum.ReportingHostSuffix.liftSet hfit S ⊆ _root_.ThreeSum.ReportingHostSuffix.liftSet hfit T ↔ S ⊆ T := Finset.map_subset_map

















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



















theorem time_bound (W n : ℕ) : _root_.ThreeSum.LightReportingSuffixSum.time W n ≤ 8000*(W+1)^2*(n+1) := by
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafGeneral.time_bound W
  have hp : 1 ≤ (W+1)^2 := Nat.one_le_pow' 2 W
  unfold _root_.ThreeSum.LightReportingSuffixSum.time
  nlinarith

end ThreeSum.LightReportingSuffixSum

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightReportingSuffixExplicit
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixExplicit

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixExplicit.meets__implementation_679b8fc7a5 {pMain pEnum pSum : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixExplicit.body pEnum pSum)) (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixExplicit.Procs P pEnum pSum)
    {μ : ℕ → ℤ} {W V offset cut stage t maskBase baseL baseR work B D d : ℕ}
    (hfit : offset+V ≤ W) (Q : Finset (Fin V)) (preL preR : Finset (Fin W))
    (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*_root_.ThreeSum.SubsetAddress.downsetCap W cut ≤ maskBase)
    (hdataR : baseR+(W+1)*_root_.ThreeSum.SubsetAddress.downsetCap W cut ≤ maskBase)
    (hmasks : maskBase+_root_.ThreeSum.SubsetAddress.layerOffset Q.card t ≤ work)
    (hspace : work+1+_root_.ThreeSum.LightPascal.tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (haccWord : (((_root_.ThreeSum.SubsetAddress.layerOffset Q.card t+1)*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word)
    (ht : t ≤ Q.card+1)
    (hcardL : (preL ∪ _root_.ThreeSum.ReportingHostSuffix.liftSet hfit Q).card ≤ cut)
    (hcardR : (preR ∪ _root_.ThreeSum.ReportingHostSuffix.liftSet hfit Q).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ D)
    (hstoredL : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseR cut g W)
    (hd : d+W+8 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d
      [W,cut,stage,preL.card,_root_.ThreeSum.SubsetAddress.subsetMask preL,preR.card,_root_.ThreeSum.SubsetAddress.subsetMask preR,V,2^offset,
        Q.card,_root_.ThreeSum.SubsetAddress.subsetMask Q,t,baseL,baseR,maskBase,work] μ (_root_.ThreeSum.LightReportingSuffixExplicit.time W Q.card t)
      (fun r μ' => r = _root_.ThreeSum.ExplicitLayers.valueSum Q (_root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage preL preR) t ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' work maskBase (_root_.ThreeSum.SubsetAddress.layerOffset Q.card t)) := by
  have hV : V ≤ W := by omega
  have hQcard : Q.card ≤ V := by simpa using Finset.card_le_univ Q
  have henumSpace : work+(2*V+2) ≤ lim.space := by
    unfold _root_.ThreeSum.LightPascal.tableSize at hspace
    nlinarith [Nat.pow_le_pow_left (Nat.succ_le_succ hV) 2]
  have henumWord : ((2^(V+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : (2^(V+1) : ℕ) ≤ (W+1)*2^(W+1) :=
      (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega)).trans
        (Nat.le_mul_of_pos_left _ (by omega))
    exact (by exact_mod_cast hh : ((2^(V+1) : ℕ) : ℤ) ≤ (((W+1)*2^(W+1) : ℕ) : ℤ)).trans hword
  have hproductWord : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤ lim.word := by
    have hh := Nat.le_mul_of_pos_left ((2^stage*B)*(2^stage*D)) (by omega : 0 < layerOffset Q.card t+1)
    exact (by exact_mod_cast hh : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤
      (((layerOffset Q.card t+1)*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ)).trans haccWord
  have hweight (S : Finset (Fin V)) (hS : S ⊆ Q) :
      |_root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage preL preR S| ≤ (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) :=
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix.leafWeight_abs_le hfit f g preL preR S hstage
      ((Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl preL)
        ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix.liftSet_subset hfit _ _).mpr hS))).trans hcardL)
      ((Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl preR)
        ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix.liftSet_subset hfit _ _).mpr hS))).trans hcardR) hf hg
  have hacc (j : ℕ) (hj : j ≤ t) :
      |_root_.ThreeSum.ExplicitLayers.valueSum Q (_root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage preL preR) j| ≤ lim.word := by
    have hh := _root_.ThreeSum1960614.Machine.ThreeSum.ExplicitLayers.valueSum_abs_le Q (_root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage preL preR) j hweight
    have hn : _root_.ThreeSum.SubsetAddress.layerOffset Q.card j*((2^stage*B)*(2^stage*D)) ≤
        (_root_.ThreeSum.SubsetAddress.layerOffset Q.card t+1)*((2^stage*B)*(2^stage*D)) :=
      Nat.mul_le_mul_right _ ((_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_mono Q.card hj).trans (Nat.le_succ _))
    have hz : ((_root_.ThreeSum.SubsetAddress.layerOffset Q.card j*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤
        (((_root_.ThreeSum.SubsetAddress.layerOffset Q.card t+1)*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) := by exact_mod_cast hn
    exact hh.trans (hz.trans haccWord)
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixExplicit.body _root_.ThreeSum.LightReportingSuffixExplicit.time
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
    (T := t*(_root_.ThreeSum.LightReportingSuffixExplicit.roundTime W Q.card t+20)+20)
    (Q := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixExplicit.Inv hfit μ Q preL preR f g stage cut t baseL baseR maskBase work t)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixExplicit.Inv hfit μ Q preL preR f g stage cut t baseL baseR maskBase work)
    t (_root_.ThreeSum.LightReportingSuffixExplicit.roundTime W Q.card t) ?start ?round ?done ?bound (hT := by (first
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
    simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]
    change _root_.Light.frame [(W : ℤ),cut,stage,preL.card,_root_.ThreeSum.SubsetAddress.subsetMask preL,preR.card,_root_.ThreeSum.SubsetAddress.subsetMask preR,V,2^offset,
      Q.card,_root_.ThreeSum.SubsetAddress.subsetMask Q,t,baseL,baseR,maskBase,work,0,0] =
      _root_.Light.frame ([(W : ℤ),cut,stage,preL.card,_root_.ThreeSum.SubsetAddress.subsetMask preL,preR.card,_root_.ThreeSum.SubsetAddress.subsetMask preR,V,2^offset,
      Q.card,_root_.ThreeSum.SubsetAddress.subsetMask Q,t,baseL,baseR,maskBase,work,0,0] ++ [0,0])
    exact (_root_.ThreeSum1960614.Machine.Light.frame_append_zeros _ 2).symm
  case round =>
    rintro j _ hj _ ⟨count,r,μ',rfl,hkeep⟩
    have hcap := _root_.ThreeSum1960614.Machine.ThreeSum.ExplicitLayers.choose_le_offset (c := Q.card) hj
    have hEnumTime : _root_.ThreeSum.LightQueryEnumeration.time V Q.card j ≤
        1400*(W+1)^2*(_root_.ThreeSum.SubsetAddress.layerOffset Q.card t+1) := by
      have hv := Nat.pow_le_pow_left (Nat.succ_le_succ hV) 2
      have hb := (_root_.ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration.time_bound hQcard).trans
        (Nat.mul_le_mul_left (1400*(V+1)^2) (Nat.succ_le_succ hcap))
      exact hb.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 1400 hv))
    have hSumTime : _root_.ThreeSum.LightReportingSuffixSum.time W (Q.card.choose j) ≤
        8000*(W+1)^2*(_root_.ThreeSum.SubsetAddress.layerOffset Q.card t+1) :=
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSum.time_bound W _).trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ hcap))
    have hp : 1 ≤ (W+1)^2*(_root_.ThreeSum.SubsetAddress.layerOffset Q.card t+1) := Nat.mul_pos (by positivity) (by omega)
    have hround : _root_.ThreeSum.LightQueryEnumeration.time V Q.card j+
        _root_.ThreeSum.LightReportingSuffixSum.time W (Q.card.choose j)+110 ≤ _root_.ThreeSum.LightReportingSuffixExplicit.roundTime W Q.card t := by
      unfold _root_.ThreeSum.LightReportingSuffixExplicit.roundTime
      nlinarith
    have he := _root_.ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration.meets (d := d+1) (μ := μ')
      (t := j) (dst := maskBase) (work := work) C.enumerate C.weights C.leafProcs.setup.powers
      C.leafProcs.erase C.core Q hw henumSpace henumWord (by omega) (by omega) (by omega)
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixExplicit.roundBody
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (he _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen he ?_ ?_ ?_ ?_
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
       on_goal -1 => (rintro newCount μ₁ ⟨hcount, hmaskSeg, _, hkeepEnum⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    have hkeep₁ : _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ₁ work maskBase (_root_.ThreeSum.SubsetAddress.layerOffset Q.card t) := by
      intro i hi
      exact (hkeepEnum i ⟨hi.1,by rcases hi.2 with h | h <;> omega⟩).trans (hkeep i hi)
    have hstoredL₁ := _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch.storedThrough_of_on hstoredL (by
      intro i _ hi
      have ha := hi.trans_le hdataL
      exact hkeep₁ i ⟨by omega,Or.inl ha⟩)
    have hstoredR₁ := _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch.storedThrough_of_on hstoredR (by
      intro i _ hi
      have ha := hi.trans_le hdataR
      exact hkeep₁ i ⟨by omega,Or.inl ha⟩)
    have hsumWord : (((_root_.ThreeSum.QueryCoordinates.missingSets Q j).length*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word := by
      have hn := Nat.mul_le_mul_right ((2^stage*B)*(2^stage*D)) (hcap.trans (Nat.le_succ _))
      have hz : ((Q.card.choose j*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤
          (((_root_.ThreeSum.SubsetAddress.layerOffset Q.card t+1)*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) := by exact_mod_cast hn
      simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.missingSets_length] using hz.trans haccWord
    have hs := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSum.meets (d := d+1) (μ := μ₁) C.sum C.leafProcs
      hfit Q preL preR (_root_.ThreeSum.QueryCoordinates.missingSets Q j) f g hw hcut hstage (by omega) (by omega)
      (by simpa using (show maskBase+Q.card.choose j ≤ work by omega)) hspace hword hproductWord hsumWord
      hcardL hcardR hf hg (fun U hU => (_root_.ThreeSum.QueryCoordinates.missingSets_mem Q U j).mp hU) hstoredL₁ hstoredR₁ hmaskSeg (by omega)
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hs _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hs ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcount, _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.missingSets_length]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hcount, _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.missingSets_length] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcount, _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.missingSets_length] <;> omega)
       on_goal -1 => (rintro res μ₂ ⟨hres, hkeepSum⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    have hnext := abs_le.mp (hacc (j+1) (by omega))
    have hres' : res = ((_root_.ThreeSum.QueryCoordinates.missingSets Q j).map fun U => _root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage preL preR (Q \ U)).sum := hres
    have hsucc := _root_.ThreeSum1960614.Machine.ThreeSum.ExplicitLayers.valueSum_succ Q (_root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage preL preR) j
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.ExplicitLayers.valueSum Q (_root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage preL preR) (j + 1)) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hres', hsucc]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hres', hsucc] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hres', hsucc] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    refine ⟨by simp,newCount,res,μ₂,?_,?_⟩
    · simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]
    · intro i hi
      exact (hkeepSum i hi.1).trans (hkeep₁ i hi)
  case done =>
    intro σ _ h
    exact h
  case bound =>
    rintro j _ hj _ ⟨count,r,μ',rfl,_⟩
    (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
  case after =>
    rintro _ ⟨count,r,μ',rfl,hkeep⟩
    have ha := abs_le.mp (hacc t le_rfl)
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.ExplicitLayers.valueSum Q (_root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage preL preR) t) ?_ ?_ ?_
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
    exact ⟨by simp,hkeep⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixExplicit.meets__implementation_679b8fc7a5) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixExplicit.meets__implementation_679b8fc7a5)

#print axioms solution
