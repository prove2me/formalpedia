-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixTable.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:33:40.051206+00:00
-- url     : https://prove2.me/submissions/0365b8df-679c-4ede-8ffa-901d45796509

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingSuffixBatch_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSubsetEnumerationSetup_meets
import Theorems.Thm_ThreeSum_SubsetAddress_enumerationWork_bound
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightDownsetAddress
end ThreeSum.LightDownsetAddress
namespace ThreeSum.LightDownsetSize
end ThreeSum.LightDownsetSize
namespace ThreeSum.LightMaskUnion
end ThreeSum.LightMaskUnion
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingSuffixBatch
end ThreeSum.LightReportingSuffixBatch
namespace ThreeSum.LightReportingSuffixCell
end ThreeSum.LightReportingSuffixCell
namespace ThreeSum.LightReportingSuffixTable
end ThreeSum.LightReportingSuffixTable
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
namespace ThreeSum.LightSubsetEnumerationSetup
end ThreeSum.LightSubsetEnumerationSetup
namespace ThreeSum.LightSubsetSetup
end ThreeSum.LightSubsetSetup
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.LightZetaPass
end ThreeSum.LightZetaPass
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.MaskUnion
end ThreeSum.MaskUnion
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightDownsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightDownsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightDownsetSize
end ThreeSum1960614.Machine.ThreeSum.LightDownsetSize
namespace ThreeSum1960614.Machine.ThreeSum.LightMaskUnion
end ThreeSum1960614.Machine.ThreeSum.LightMaskUnion
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixBatch
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixBatch
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCell
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCell
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixTable
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixTable
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
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumerationSetup
end ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumerationSetup
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup
end ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaCell
end ThreeSum1960614.Machine.ThreeSum.LightZetaCell
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaPass
end ThreeSum1960614.Machine.ThreeSum.LightZetaPass
namespace ThreeSum1960614.Machine.ThreeSum.MaskDecode
end ThreeSum1960614.Machine.ThreeSum.MaskDecode
namespace ThreeSum1960614.Machine.ThreeSum.MaskErase
end ThreeSum1960614.Machine.ThreeSum.MaskErase
namespace ThreeSum1960614.Machine.ThreeSum.MaskUnion
end ThreeSum1960614.Machine.ThreeSum.MaskUnion
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

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

/-- More time and a weaker conclusion. -/
theorem Meets.mono (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (hT : T ≤ T') (hR : ∀ r μ', R r μ' → R' r μ') :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T' R' := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, hp, he.mono hT fun _ => hR _ _⟩

/-- A specification holds with every larger bound on the time. -/
theorem Meets.mono_time (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (hT : T ≤ T' := by omega) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T' R :=
  h.mono hT fun _ _ hR => hR





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
# A fixed subset-layer enumerator with its own power-table construction

The main theorem has no supplied lookup-table correctness assumption. The
only auxiliary memory is a table of `L+1` powers of two, built once before
the recursive enumeration. The output has exactly `L.choose k` cells.
-/

namespace ThreeSum.LightSubsetEnumerationSetup
open _root_.ThreeSum.LightSubsetEnumerationSetup


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}











theorem time_bound (L k : ℕ) : _root_.ThreeSum.LightSubsetEnumerationSetup.time L k ≤ 800*(L+1)*(L.choose k+1) := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.time_bound L k
  unfold _root_.ThreeSum.LightSubsetEnumerationSetup.time _root_.Light.powTableTime
  nlinarith

end ThreeSum.LightSubsetEnumerationSetup

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A complete coordinate pass over a compact downset

For each stored cardinality the fixed procedure constructs its layer of
masks, then runs the compact-cell update on that layer. Only the compact
downset and polynomial workspace are allocated; the program never visits
all integers below `2^L`. The source table remains unchanged throughout
the pass.
-/

namespace ThreeSum.LightZetaPass
open _root_.ThreeSum.LightZetaPass


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightZetaCell
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}





theorem choose_le_cap {L cut j : ℕ} (hcut : cut ≤ L) (hj : j ≤ cut) :
    L.choose j ≤ _root_.ThreeSum.SubsetAddress.downsetCap L cut := by
  have ho := _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_mono L (show j+1 ≤ min cut L+1 by omega)
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ] at ho
  unfold _root_.ThreeSum.SubsetAddress.downsetCap
  omega





















end ThreeSum.LightZetaPass

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











theorem values_layer {W cardinal : ℕ} (μ : ℕ → ℤ) (dst : ℕ)
    (weight : Finset (Fin W) → ℤ) (S : Finset (Fin W)) :
    _root_.ThreeSum.LightSignedLeafBatch.values μ dst (_root_.ThreeSum.SubsetAddress.enumerateLayer W cardinal) weight S =
      if S.card = cardinal then weight S else μ (dst+_root_.ThreeSum.SubsetAddress.subsetRank S) := by
  have hm := _root_.ThreeSum.SubsetAddress.subsetMask_isMask S
  simp only [_root_.ThreeSum.LightSignedLeafBatch.values,_root_.ThreeSum.SubsetAddress.mem_enumerateLayer,_root_.ThreeSum.SubsetAddress.IsMask,hm.1,true_and,hm.2]



end ThreeSum.LightSignedLeafBatch

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















theorem time_bound {W V : ℕ} (hV : V ≤ W) : _root_.ThreeSum.LightReportingSuffixCell.time W V ≤ 9300*(W+1)^2 := by
  have hl := _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafGeneral.time_bound W
  have ha := _root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetAddress.time_bound V
  have hp := Nat.pow_le_pow_left (Nat.succ_le_succ hV) 2
  have hpos : 1 ≤ (W+1)^2 := Nat.one_le_pow' 2 W
  unfold _root_.ThreeSum.LightReportingSuffixCell.time
  nlinarith

end ThreeSum.LightReportingSuffixCell

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Evaluating one locally enumerated suffix layer against global source tables -/

namespace ThreeSum.LightReportingSuffixBatch
open _root_.ThreeSum.LightReportingSuffixBatch


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightZetaCell
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell
open _root_.ThreeSum.MaskDecode
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskDecode
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}









theorem time_bound {W V : ℕ} (hV : V ≤ W) (n : ℕ) :
    _root_.ThreeSum.LightReportingSuffixBatch.time W V n ≤ 9400*(W+1)^2*(n+1) := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCell.time_bound hV
  have hmul := Nat.mul_le_mul_left n h
  have hpoly : 1 ≤ (W+1)^2 := Nat.one_le_pow' 2 W
  have hsmall := Nat.mul_le_mul_left n (show 65 ≤ 100*(W+1)^2 by omega)
  unfold _root_.ThreeSum.LightReportingSuffixBatch.time
  nlinarith

end ThreeSum.LightReportingSuffixBatch

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightReportingSuffixTable
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixTable

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightZetaCell
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixTable.meets__implementation_071468fb09 {pMain pEnumSetup pEnum pBatch pCell pLeaf pAddress : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixTable.body pEnumSetup pBatch))
    (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafCell.Procs P pLeaf pAddress)
    (hEnumSetup : P[pEnumSetup]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumerationSetup.body C.pPowers pEnum))
    (hEnum : P[pEnum]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.body pEnum))
    (hBatch : P[pBatch]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixBatch.body pCell))
    (hCell : P[pCell]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCell.body pLeaf pAddress))
    {μ : ℕ → ℤ} {W V offset sourceCut boxCut stage baseL baseR dst maskBase work B D d : ℕ}
    (hfit : offset+V ≤ W) (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : sourceCut ≤ W) (hboxCut : boxCut ≤ V)
    (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*_root_.ThreeSum.SubsetAddress.downsetCap W sourceCut ≤ maskBase)
    (hdataR : baseR+(W+1)*_root_.ThreeSum.SubsetAddress.downsetCap W sourceCut ≤ maskBase)
    (hdst : dst+_root_.ThreeSum.SubsetAddress.downsetCap V boxCut ≤ maskBase)
    (hmasks : maskBase+_root_.ThreeSum.SubsetAddress.downsetCap V boxCut ≤ work)
    (hsepL : _root_.Light.Apart baseL ((W+1)*_root_.ThreeSum.SubsetAddress.downsetCap W sourceCut) dst (_root_.ThreeSum.SubsetAddress.downsetCap V boxCut))
    (hsepR : _root_.Light.Apart baseR ((W+1)*_root_.ThreeSum.SubsetAddress.downsetCap W sourceCut) dst (_root_.ThreeSum.SubsetAddress.downsetCap V boxCut))
    (hspace : work+1+_root_.ThreeSum.LightPascal.tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hproductWord : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤ lim.word)
    (hpreL : preL.card+boxCut ≤ sourceCut) (hpreR : preR.card+boxCut ≤ sourceCut)
    (hf : ∀ T, T.card ≤ sourceCut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ sourceCut → |g T| ≤ D)
    (hstoredL : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseL sourceCut f W)
    (hstoredR : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseR sourceCut g W)
    (hd : d+W+9 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d
      [W,sourceCut,boxCut,stage,preL.card,_root_.ThreeSum.SubsetAddress.subsetMask preL,preR.card,_root_.ThreeSum.SubsetAddress.subsetMask preR,
        V,2^offset,baseL,baseR,dst,maskBase,work] μ (_root_.ThreeSum.LightReportingSuffixTable.time W V boxCut)
      (fun _ μ' => _root_.ThreeSum.LightZetaCell.TableAt μ' dst boxCut (_root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage preL preR) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' maskBase dst (_root_.ThreeSum.SubsetAddress.downsetCap V boxCut)) := by
  have hV : V ≤ W := by omega
  have hword₀ : ((2^(V+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : (2^(V+1) : ℕ) ≤ (W+1)*2^(W+1) :=
      (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega)).trans
        (Nat.le_mul_of_pos_left _ (by omega))
    exact (by exact_mod_cast hh : ((2^(V+1) : ℕ) : ℤ) ≤
      (((W+1)*2^(W+1) : ℕ) : ℤ)).trans hword
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixTable.body _root_.ThreeSum.LightReportingSuffixTable.time
  refine _root_.ThreeSum1960614.Machine.Light.Ends.for (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixTable.Inv hfit μ sourceCut boxCut stage baseL baseR dst maskBase work preL preR f g)
    (boxCut+1) (_root_.ThreeSum.LightReportingSuffixTable.roundBudget W V boxCut) ?start ?round ?done ?bound (hT := by (first
                                                                                                                        | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                                                                            first
                                                                                                                            | omega
                                                                                                                            | (ring_nf; omega))
                                                                                                                        | omega
                                                                                                                        |
                                                                                                                          (simp [] <;>
                                                                                                                              first
                                                                                                                              | omega
                                                                                                                              | (ring_nf; omega))))
  case start =>
    refine ⟨0,0,μ,?_,_root_.ThreeSum1960614.Machine.Light.SameOn.refl,?_⟩
    · simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]
      change _root_.Light.frame [(W : ℤ),sourceCut,boxCut,stage,preL.card,_root_.ThreeSum.SubsetAddress.subsetMask preL,preR.card,_root_.ThreeSum.SubsetAddress.subsetMask preR,
        V,2^offset,baseL,baseR,dst,maskBase,work,0] =
        _root_.Light.frame ([(W : ℤ),sourceCut,boxCut,stage,preL.card,_root_.ThreeSum.SubsetAddress.subsetMask preL,preR.card,_root_.ThreeSum.SubsetAddress.subsetMask preR,
          V,2^offset,baseL,baseR,dst,maskBase,work,0] ++ [0,0])
      exact (_root_.ThreeSum1960614.Machine.Light.frame_append_zeros _ 2).symm
    · intro S hS
      simp [_root_.ThreeSum.LightSignedLeafTable.stageValues]
  case round =>
    rintro j _ hj _ ⟨n,r,μ',rfl,hkept,hout⟩
    have hjcut : j ≤ boxCut := by omega
    have hchoose := _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaPass.choose_le_cap hboxCut hjcut
    have hsourceL : _root_.ThreeSum.LightZetaStages.StoredThrough μ' baseL sourceCut f W :=
      _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch.storedThrough_of_on hstoredL (by
        intro i hi₀ hi₁
        exact hkept i ⟨by omega,by omega⟩)
    have hsourceR : _root_.ThreeSum.LightZetaStages.StoredThrough μ' baseR sourceCut g W :=
      _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch.storedThrough_of_on hstoredR (by
        intro i hi₀ hi₁
        exact hkept i ⟨by omega,by omega⟩)
    have hen := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumerationSetup.meets (d := d+1) hEnumSetup C.setup.powers hEnum
      (μ := μ') (L := V) (k := j) (dst := maskBase) (work := work)
      hw (by omega) hword₀ (by omega) (by omega) (by omega)
    have hentime : _root_.ThreeSum.LightSubsetEnumerationSetup.time V j ≤ _root_.ThreeSum.LightReportingSuffixTable.enumBudget V boxCut :=
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumerationSetup.time_bound V j).trans
        (Nat.mul_le_mul_left (800*(V+1)) (Nat.succ_le_succ hchoose))
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixTable.roundBody _root_.ThreeSum.LightReportingSuffixTable.roundBudget
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((hen.mono_time hentime) _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hen.mono_time hentime) ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingSuffixTable.enumBudget, _root_.ThreeSum.LightReportingSuffixTable.batchBudget]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum.LightReportingSuffixTable.enumBudget, _root_.ThreeSum.LightReportingSuffixTable.batchBudget] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightReportingSuffixTable.enumBudget, _root_.ThreeSum.LightReportingSuffixTable.batchBudget] <;> omega)
       on_goal -1 => (rintro count μ₁ ⟨hcount, hseg, hpowers, henkept⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    have hsourceL₁ : _root_.ThreeSum.LightZetaStages.StoredThrough μ₁ baseL sourceCut f W :=
      _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch.storedThrough_of_on hsourceL (by
        intro i hi₀ hi₁
        exact henkept i ⟨by omega,Or.inl (by omega)⟩)
    have hsourceR₁ : _root_.ThreeSum.LightZetaStages.StoredThrough μ₁ baseR sourceCut g W :=
      _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch.storedThrough_of_on hsourceR (by
        intro i hi₀ hi₁
        exact henkept i ⟨by omega,Or.inl (by omega)⟩)
    have hb := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixBatch.meets (d := d+1) hBatch hCell C hfit
      (_root_.ThreeSum.SubsetAddress.enumerateLayer V j) preL preR f g hw hcut hstage (by omega) (by omega) (by omega)
      (by rw [_root_.ThreeSum.SubsetAddress.enumerateLayer_length]; omega) hsepL hsepR (Or.inr hdst)
      hspace hword hproductWord hpreL hpreR hf hg hsourceL₁ hsourceR₁ hseg
      (fun m hm => (_root_.ThreeSum.SubsetAddress.mem_enumerateLayer V j m).mp hm) hjcut (by omega)
    have hbtime : _root_.ThreeSum.LightReportingSuffixBatch.time W V (_root_.ThreeSum.SubsetAddress.enumerateLayer V j).length ≤ _root_.ThreeSum.LightReportingSuffixTable.batchBudget W V boxCut := by
      rw [_root_.ThreeSum.SubsetAddress.enumerateLayer_length]
      exact (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixBatch.time_bound hV (V.choose j)).trans
        (Nat.mul_le_mul_left (9400*(W+1)^2) (Nat.succ_le_succ hchoose))
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((hb.mono_time hbtime) _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hb.mono_time hbtime) ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcount, _root_.ThreeSum.SubsetAddress.enumerateLayer_length, _root_.ThreeSum.LightReportingSuffixTable.enumBudget, _root_.ThreeSum.LightReportingSuffixTable.batchBudget]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hcount, _root_.ThreeSum.SubsetAddress.enumerateLayer_length, _root_.ThreeSum.LightReportingSuffixTable.enumBudget, _root_.ThreeSum.LightReportingSuffixTable.batchBudget] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcount, _root_.ThreeSum.SubsetAddress.enumerateLayer_length, _root_.ThreeSum.LightReportingSuffixTable.enumBudget, _root_.ThreeSum.LightReportingSuffixTable.batchBudget] <;> omega)
       on_goal -1 => (rintro res μ₂ ⟨hnew, hbkept⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    refine ⟨by simp,count,res,μ₂,?_,?_,?_⟩
    · simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]
    · intro i hi
      exact (hbkept i ⟨by omega,hi.2⟩).trans
        ((henkept i ⟨by omega,Or.inl hi.1⟩).trans (hkept i hi))
    · intro T hT
      have hr := _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.subsetRank_lt hT
      have hn := hnew T hT
      rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch.values_layer] at hn
      have hbefore : μ₁ (dst+_root_.ThreeSum.SubsetAddress.subsetRank T) = μ' (dst+_root_.ThreeSum.SubsetAddress.subsetRank T) :=
        henkept _ ⟨by omega,Or.inl (by omega)⟩
      by_cases heq : T.card = j
      · have hlt : T.card < j+1 := by omega
        simpa only [_root_.ThreeSum.LightSignedLeafTable.stageValues,heq,ite_true,show j < j+1 by omega] using hn
      · rw [if_neg heq,hbefore,hout T hT] at hn
        have hlt : T.card < j+1 ↔ T.card < j := by omega
        simpa only [_root_.ThreeSum.LightSignedLeafTable.stageValues,hlt] using hn
  case done =>
    rintro _ _ ⟨n,r,μ',rfl,hkept,hout⟩
    refine ⟨?_,hkept⟩
    intro T hT
    simpa only [_root_.ThreeSum.LightSignedLeafTable.stageValues,show T.card < boxCut+1 by omega,ite_true] using hout T hT
  case bound =>
    rintro j _ hj _ ⟨n,r,μ',rfl,_,_⟩
    (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixTable.meets__implementation_071468fb09) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixTable.meets__implementation_071468fb09)

#print axioms solution
