-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightQueryBox.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:15:35.79089+00:00
-- url     : https://prove2.me/submissions/b9188391-1901-4657-a96f-6e1552c33058

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
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightMaskMinimum_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightStageLookup_meets
import Theorems.Thm_ThreeSum_BoxStages_partialZeta_eq_boxSum
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_union_sdiff
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BoxStages
end ThreeSum.BoxStages
namespace ThreeSum.LightBoxStages
end ThreeSum.LightBoxStages
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightQueryBox
end ThreeSum.LightQueryBox
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.MaskDifference
end ThreeSum.MaskDifference
namespace ThreeSum.SparseBoxes
end ThreeSum.SparseBoxes
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BoxStages
end ThreeSum1960614.Machine.ThreeSum.BoxStages
namespace ThreeSum1960614.Machine.ThreeSum.LightBoxStages
end ThreeSum1960614.Machine.ThreeSum.LightBoxStages
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightQueryBox
end ThreeSum1960614.Machine.ThreeSum.LightQueryBox
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaCell
end ThreeSum1960614.Machine.ThreeSum.LightZetaCell
namespace ThreeSum1960614.Machine.ThreeSum.MaskDifference
end ThreeSum1960614.Machine.ThreeSum.MaskDifference
namespace ThreeSum1960614.Machine.ThreeSum.SparseBoxes
end ThreeSum1960614.Machine.ThreeSum.SparseBoxes
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

namespace ThreeSum1960614.Machine

/-!
# Finite sparse-query boxes

The largest-missing-element partition and the reusable box recurrence are proved
here as exact finite identities.  The accompanying cardinalities concern the
actual canonical box family, not the family of all arbitrary free-coordinate
subsets.
-/

namespace ThreeSum.SparseBoxes
open _root_.ThreeSum.SparseBoxes


open scoped _root_.BigOperators

variable {α : Type*} [LinearOrder α]















theorem queryFree_eq_filter_min (q u : Finset α) (hu : u.Nonempty) :
    _root_.ThreeSum.SparseBoxes.queryFree q u = (q \ u).filter (fun x => x < u.min' hu) := by
  ext x
  simp only [_root_.ThreeSum.SparseBoxes.queryFree, Finset.mem_filter]
  constructor
  · rintro ⟨hx, ho⟩
    exact ⟨hx, ho _ (Finset.min'_mem u hu)⟩
  · rintro ⟨hx, ho⟩
    refine ⟨hx, ?_⟩
    intro y hy
    exact ho.trans_le (Finset.min'_le u y hy)









/-! ## Canonical free prefixes and the finite preprocessing family -/



































/-! ## The exact addition recurrence and query sum -/





















/-! ## Number of query accesses -/













end ThreeSum.SparseBoxes

end ThreeSum1960614.Machine

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















theorem Ends.ite {σ T c s₁ s₂} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} (T' : ℕ) (hs : c.Safe lim σ)
    (h₁ : c.Holds σ → _root_.ThreeSum1960614.Machine.Light.Ends lim P d s₁ σ T' Q) (h₂ : ¬ c.Holds σ → _root_.ThreeSum1960614.Machine.Light.Ends lim P d s₂ σ T' Q)
    (hT : c.cost + 1 + T' ≤ T) : _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.ite c s₁ s₂) σ T Q := by
  by_cases hv : c.Holds σ
  · obtain ⟨σ', k, he, hk, hq⟩ := h₁ hv
    exact ⟨σ', _, _root_.ThreeSum1960614.Machine.Light.Exec.iteTrue hs hv he, by omega, hq⟩
  · obtain ⟨σ', k, he, hk, hq⟩ := h₂ hv
    exact ⟨σ', _, _root_.ThreeSum1960614.Machine.Light.Exec.iteFalse hs hv he, by omega, hq⟩













/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/


















/-! ## Simplification -/

attribute [simp] _root_.ThreeSum1960614.Machine.Light.Expr.val _root_.ThreeSum1960614.Machine.Light.Expr.cost _root_.ThreeSum1960614.Machine.Light.Expr.Safe _root_.Light.Op.eval _root_.ThreeSum1960614.Machine.Light.Cond.Holds _root_.ThreeSum1960614.Machine.Light.Cond.cost _root_.ThreeSum1960614.Machine.Light.Cond.Safe _root_.Light.frame







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
# Canonical sparse boxes as stored prefix-zeta stages

A global coordinate prefix intersects each flagged set in an initial
segment. Storing those initialCoords stages uses only a polynomial factor more
than the compact downset. The resulting entries are exactly the signed
box sums used by the sparse-query partition.
-/

namespace ThreeSum.BoxStages
open _root_.ThreeSum.BoxStages


open _root_.Finset



@[simp] theorem mem_prefix {L j : ℕ} (a : Fin L) : a ∈ _root_.ThreeSum.BoxStages.initialCoords L j ↔ a.val < j := by
  simp [_root_.ThreeSum.BoxStages.initialCoords]



@[simp] theorem prefix_all (L : ℕ) : _root_.ThreeSum.BoxStages.initialCoords L L = univ := by
  ext a
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BoxStages.mem_prefix,mem_univ,iff_true]
  exact a.isLt



















theorem stageValue_eq_boxSum {L : ℕ} (weight : Finset (Fin L) → ℤ)
    (j : ℕ) (flags : Finset (Fin L)) :
    _root_.ThreeSum.BoxStages.stageValue weight j flags = _root_.ThreeSum.SparseBoxes.boxSum flags (flags ∩ _root_.ThreeSum.BoxStages.initialCoords L j) weight :=
  _root_.ThreeSum.BoxStages.partialZeta_eq_boxSum weight flags (_root_.ThreeSum.BoxStages.initialCoords L j)

theorem queryFree_prefix {L : ℕ} (q u : Finset (Fin L)) (hu : u.Nonempty) :
    _root_.ThreeSum.SparseBoxes.queryFree q u = (q \ u) ∩ _root_.ThreeSum.BoxStages.initialCoords L (u.min' hu).val := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SparseBoxes.queryFree_eq_filter_min q u hu]
  ext a
  simp only [mem_filter,mem_inter,_root_.ThreeSum1960614.Machine.ThreeSum.BoxStages.mem_prefix]
  rfl

theorem query_box_stage {L : ℕ} (weight : Finset (Fin L) → ℤ)
    (q u : Finset (Fin L)) (hu : u.Nonempty) :
    _root_.ThreeSum.SparseBoxes.boxSum (q \ u) (_root_.ThreeSum.SparseBoxes.queryFree q u) weight =
      _root_.ThreeSum.BoxStages.stageValue weight (u.min' hu).val (q \ u) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BoxStages.queryFree_prefix q u hu,_root_.ThreeSum1960614.Machine.ThreeSum.BoxStages.stageValue_eq_boxSum]

end ThreeSum.BoxStages

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

@[simp] theorem subsetMask_empty (L : ℕ) : _root_.ThreeSum.SubsetAddress.subsetMask (∅ : Finset (Fin L)) = 0 := by
  simp [_root_.ThreeSum1960614.Machine.ThreeSum.MaskDifference.subsetMask_sum]

theorem subsetMask_eq_zero_iff {L : ℕ} (S : Finset (Fin L)) :
    _root_.ThreeSum.SubsetAddress.subsetMask S = 0 ↔ S = ∅ := by
  constructor
  · intro h
    exact _root_.ThreeSum.SubsetAddress.subsetMask_injective L (h.trans (_root_.ThreeSum1960614.Machine.ThreeSum.MaskDifference.subsetMask_empty L).symm)
  · rintro rfl
    exact _root_.ThreeSum1960614.Machine.ThreeSum.MaskDifference.subsetMask_empty L





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
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Blocks -/











/-! ## The default proofs -/











/-! ## Rules for blocks -/













/-! ## Sequencing: what is left of the time goes to the rest of the program -/























/-- A branch at the end of the program: both sides get the steps that the test leaves. -/
theorem Ends.iteLast {σ : _root_.ThreeSum1960614.Machine.Light.State} {T : ℕ} {c : _root_.ThreeSum1960614.Machine.Light.Cond} {s₁ s₂ : _root_.ThreeSum1960614.Machine.Light.Stmt} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}
    (h₁ : c.Holds σ → _root_.ThreeSum1960614.Machine.Light.Ends lim P d s₁ σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → _root_.ThreeSum1960614.Machine.Light.Ends lim P d s₂ σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ := by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))) (hT : c.cost + 1 ≤ T := by (first
                                                                     | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                         first
                                                                         | omega
                                                                         | (ring_nf; omega))
                                                                     | omega
                                                                     |
                                                                       (simp [] <;>
                                                                           first
                                                                           | omega
                                                                           | (ring_nf; omega)))) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.ite c s₁ s₂) σ T Q :=
  _root_.ThreeSum1960614.Machine.Light.Ends.ite _ hs h₁ h₂ (by omega)





/-! ## Loops whose body is a block -/



/-! ## Counting loops -/







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
# Building and retaining every compact prefix-zeta stage

The fixed program computes the compact table stride, then makes one
coordinate pass per bit. All earlier stages remain available for canonical
sparse-box queries. Its workspace is `(L+2)*downsetCap + O(L^2)`, and its
time is a polynomial in `L` times `downsetCap`. Intermediate word bounds
are derived from the original table values.
-/

namespace ThreeSum.LightBoxStages
open _root_.ThreeSum.LightBoxStages


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.BoxStages
open _root_.ThreeSum1960614.Machine.ThreeSum.BoxStages
open _root_.ThreeSum.LightZetaCell
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}























theorem stored_box_lookup {μ : ℕ → ℤ} {L cut base j : ℕ}
    {weight : Finset (Fin L) → ℤ} (h : _root_.ThreeSum.LightBoxStages.StoredThrough μ base cut weight L) (hj : j ≤ L)
    (flags : Finset (Fin L)) (hflags : flags.card ≤ cut) :
    μ (_root_.ThreeSum.LightBoxStages.stageBase base (_root_.ThreeSum.SubsetAddress.downsetCap L cut) j+_root_.ThreeSum.SubsetAddress.subsetRank flags) =
      _root_.ThreeSum.SparseBoxes.boxSum flags (flags ∩ _root_.ThreeSum.BoxStages.initialCoords L j) weight := by
  rw [h j hj flags hflags]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BoxStages.stageValue_eq_boxSum weight j flags

theorem stored_query_box {μ : ℕ → ℤ} {L cut base : ℕ}
    {weight : Finset (Fin L) → ℤ} (h : _root_.ThreeSum.LightBoxStages.StoredThrough μ base cut weight L)
    (q u : Finset (Fin L)) (hu : u.Nonempty) (hflags : (q \ u).card ≤ cut) :
    μ (_root_.ThreeSum.LightBoxStages.stageBase base (_root_.ThreeSum.SubsetAddress.downsetCap L cut) (u.min' hu).val+_root_.ThreeSum.SubsetAddress.subsetRank (q \ u)) =
      _root_.ThreeSum.SparseBoxes.boxSum (q \ u) (_root_.ThreeSum.SparseBoxes.queryFree q u) weight := by
  rw [h (u.min' hu).val (Nat.le_of_lt (u.min' hu).isLt) (q \ u) hflags]
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.BoxStages.query_box_stage weight q u hu).symm



end ThreeSum.LightBoxStages

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightQueryBox
open _root_.ThreeSum1960614.Machine.ThreeSum.LightQueryBox

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.MaskDifference
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskDifference
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightQueryBox.meets__implementation_47d28a7e07
    {pMain pMinimum pLookup pSize pAddress pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightQueryBox.body pMinimum pLookup))
    (hMinimum : P[pMinimum]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskMinimum.body pPowers pErase))
    (hLookup : P[pLookup]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightStageLookup.body pSize pAddress))
    (hSize : P[pSize]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.body pSetup pOffset))
    (hAddress : P[pAddress]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetAddress.body pSetup pOffset))
    (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset.body)
    (hErase : P[pErase]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L cut base work d : ℕ}
    (Q U : Finset (Fin L)) (weight : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hdata : base+(L+1)*_root_.ThreeSum.SubsetAddress.downsetCap L cut ≤ work)
    (hspace : work+_root_.ThreeSum.LightPascal.tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hU : U ⊆ Q) (hflags : (Q \ U).card ≤ cut)
    (hstored : _root_.ThreeSum.LightBoxStages.StoredThrough μ base cut weight L)
    (hd : d+L+6 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [L,cut,Q.card,_root_.ThreeSum.SubsetAddress.subsetMask Q,U.card,_root_.ThreeSum.SubsetAddress.subsetMask U,base,work] μ (_root_.ThreeSum.LightQueryBox.time L)
      (fun r μ' => r = _root_.ThreeSum.SparseBoxes.boxSum (Q \ U) (_root_.ThreeSum.SparseBoxes.queryFree Q U) weight ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ μ' work) := by
  have hword₀ : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : (2^(L+1) : ℕ) ≤ (L+1)*2^(L+1) := Nat.le_mul_of_pos_left _ (by omega)
    exact (by exact_mod_cast hh : ((2^(L+1) : ℕ) : ℤ) ≤
      (((L+1)*2^(L+1) : ℕ) : ℤ)).trans hword
  have hpow : (2^L : ℕ) ≤ 2^(L+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hpowZ : ((2^L : ℕ) : ℤ) ≤ lim.word :=
    (by exact_mod_cast hpow : ((2^L : ℕ) : ℤ) ≤ ((2^(L+1) : ℕ) : ℤ)).trans hword₀
  have hcardle := Finset.card_le_card hU
  have hcardDiff := Finset.card_sdiff_of_subset hU
  have hcard : (Q.card : ℤ)-(U.card : ℤ) = ((Q \ U).card : ℤ) := by omega
  have hmask := _root_.ThreeSum1960614.Machine.ThreeSum.MaskDifference.subsetMask_sdiff_int Q U hU
  have hmaskBound : (_root_.ThreeSum.SubsetAddress.subsetMask (Q \ U) : ℤ) < ((2^L : ℕ) : ℤ) := by
    exact_mod_cast (_root_.ThreeSum.SubsetAddress.subsetMask_isMask (Q \ U)).1
  have hmaskNonneg : (0 : ℤ) ≤ _root_.ThreeSum.SubsetAddress.subsetMask (Q \ U) := Int.natCast_nonneg _
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.subsetRank_lt hflags
  have haddr (j : ℕ) (hj : j ≤ L) : _root_.ThreeSum.LightStageLookup.readAddr cut base j (Q \ U) < work := by
    have hm := Nat.mul_le_mul_right (_root_.ThreeSum.SubsetAddress.downsetCap L cut) (Nat.succ_le_succ hj)
    unfold _root_.ThreeSum.LightStageLookup.readAddr
    simp only [Nat.succ_mul,Nat.add_mul,Nat.one_mul] at hm hdata
    omega
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightQueryBox.body _root_.ThreeSum.LightQueryBox.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen ((Q \ U).card : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcard, _root_.ThreeSum.LightMaskMinimum.time, _root_.ThreeSum.LightStageLookup.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hcard, _root_.ThreeSum.LightMaskMinimum.time, _root_.ThreeSum.LightStageLookup.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcard, _root_.ThreeSum.LightMaskMinimum.time, _root_.ThreeSum.LightStageLookup.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SubsetAddress.subsetMask (Q \ U) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hmask, _root_.ThreeSum.LightMaskMinimum.time, _root_.ThreeSum.LightStageLookup.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hmask, _root_.ThreeSum.LightMaskMinimum.time, _root_.ThreeSum.LightStageLookup.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hmask, _root_.ThreeSum.LightMaskMinimum.time, _root_.ThreeSum.LightStageLookup.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  refine _root_.ThreeSum1960614.Machine.Light.Ends.pieceThen (_root_.ThreeSum1960614.Machine.Light.Ends.iteLast
    (T := _root_.ThreeSum.LightMaskMinimum.time L+20)
    (Q := fun σ => ∃ (j : ℕ), j ≤ L ∧
      σ.loc = _root_.Light.frame (_root_.Light.setLocal (_root_.Light.setLocal (_root_.Light.setLocal
        [L,cut,Q.card,_root_.ThreeSum.SubsetAddress.subsetMask Q,U.card,_root_.ThreeSum.SubsetAddress.subsetMask U,base,work]
        8 ((Q \ U).card : ℤ)) 9 (_root_.ThreeSum.SubsetAddress.subsetMask (Q \ U) : ℤ)) 10 (j : ℤ)) ∧
      _root_.ThreeSum1960614.Machine.Light.Kept μ σ.mem work ∧
      σ.mem (_root_.ThreeSum.LightStageLookup.readAddr cut base j (Q \ U)) =
        _root_.ThreeSum.SparseBoxes.boxSum (Q \ U) (_root_.ThreeSum.SparseBoxes.queryFree Q U) weight)
    ?zero ?nonzero (by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))) (hT := by (first
                                              | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightMaskMinimum.time]
                                                  first
                                                  | omega
                                                  | (ring_nf; omega))
                                              | omega
                                              |
                                                (simp [_root_.ThreeSum.LightMaskMinimum.time] <;>
                                                    first
                                                    | omega
                                                    | (ring_nf; omega)))))
    ?after (hT := by (first
                      | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightMaskMinimum.time, _root_.ThreeSum.LightStageLookup.time]
                          first
                          | omega
                          | (ring_nf; omega))
                      | omega
                      |
                        (simp [_root_.ThreeSum.LightMaskMinimum.time, _root_.ThreeSum.LightStageLookup.time] <;>
                            first
                            | omega
                            | (ring_nf; omega))))
  case zero =>
    intro hz
    have hz' : _root_.ThreeSum.SubsetAddress.subsetMask U = 0 := by exact_mod_cast (by simpa using hz : (subsetMask U : ℤ) = 0)
    have hUempty := (_root_.ThreeSum1960614.Machine.ThreeSum.MaskDifference.subsetMask_eq_zero_iff U).mp hz'
    have hread : μ (_root_.ThreeSum.LightStageLookup.readAddr cut base L (Q \ U)) =
        _root_.ThreeSum.SparseBoxes.boxSum (Q \ U) (_root_.ThreeSum.SparseBoxes.queryFree Q U) weight := by
      have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightBoxStages.stored_box_lookup hstored le_rfl (Q \ U) hflags
      simpa [_root_.ThreeSum.LightStageLookup.readAddr,_root_.ThreeSum.LightBoxStages.stageBase,_root_.ThreeSum.SparseBoxes.queryFree,hUempty] using hh
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (L : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightMaskMinimum.time, _root_.ThreeSum.LightStageLookup.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum.LightMaskMinimum.time, _root_.ThreeSum.LightStageLookup.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightMaskMinimum.time, _root_.ThreeSum.LightStageLookup.time] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    exact ⟨L,le_rfl,rfl,_root_.ThreeSum1960614.Machine.Light.SameOn.refl,hread⟩
  case nonzero =>
    intro hz
    have hUpos : U.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro he
      apply hz
      simp [he,_root_.ThreeSum1960614.Machine.ThreeSum.MaskDifference.subsetMask_empty]
    have hm := _root_.ThreeSum1960614.Machine.ThreeSum.LightMaskMinimum.meets (d := d+1) (μ := μ) (work := work)
      hMinimum C.powers hErase U hUpos
      hw (by omega) hword₀ (by omega)
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hm _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hm ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightMaskMinimum.time, _root_.ThreeSum.LightStageLookup.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum.LightMaskMinimum.time, _root_.ThreeSum.LightStageLookup.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightMaskMinimum.time, _root_.ThreeSum.LightStageLookup.time] <;> omega)
       on_goal -1 => (rintro smallest μ₁ ⟨hsmallest, hminKept⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    refine ⟨(U.min' hUpos).val,Nat.le_of_lt (U.min' hUpos).isLt,?_,hminKept,?_⟩
    · simp only [hsmallest]
    · have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightBoxStages.stored_query_box hstored Q U hUpos hflags
      exact (hminKept _ (haddr _ (Nat.le_of_lt (U.min' hUpos).isLt))).trans hh
  case after =>
    rintro σ ⟨j,hj,hloc,hkept,hread⟩
    rcases σ with ⟨loc,μ'⟩
    simp only at hloc hkept hread
    subst loc
    have hc := _root_.ThreeSum1960614.Machine.ThreeSum.LightStageLookup.meets (d := d+1) hLookup hSize hAddress C hOffset
      (Q \ U) (_root_.ThreeSum.SparseBoxes.boxSum (Q \ U) (_root_.ThreeSum.SparseBoxes.queryFree Q U) weight)
      hw hcut hdata hspace hword hflags hj hread (by omega)
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
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightMaskMinimum.time, _root_.ThreeSum.LightStageLookup.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum.LightMaskMinimum.time, _root_.ThreeSum.LightStageLookup.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightMaskMinimum.time, _root_.ThreeSum.LightStageLookup.time] <;> omega)
       on_goal -1 => (rintro res μ₁ ⟨hres, hnewKept⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    exact ⟨hres,hkept.trans hnewKept⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightQueryBox.meets__implementation_47d28a7e07) := (@ThreeSum1960614.Machine.ThreeSum.LightQueryBox.meets__implementation_47d28a7e07)

#print axioms solution
