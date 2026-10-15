-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:45:10.558741+00:00
-- url     : https://prove2.me/submissions/184b758c-d86b-4b81-92a0-4408f2f26e86

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
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
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
import Definitions.Def_ThreeSum1960614_Machine_Bundle027
import Definitions.Def_ThreeSum1960614_Machine_Bundle028
import Definitions.Def_ThreeSum1960614_Machine_Bundle029
import Definitions.Def_ThreeSum1960614_Machine_Bundle030
import Definitions.Def_ThreeSum1960614_Machine_Bundle031
import Definitions.Def_ThreeSum1960614_Machine_Bundle032
import Definitions.Def_ThreeSum1960614_Machine_Bundle033
import Definitions.Def_ThreeSum1960614_Machine_Bundle034
import Definitions.Def_ThreeSum1960614_Machine_Bundle035
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
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
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
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum1960614_LightQuarticSwitch_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSharedReportingCell_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSharedReportingLoop_forSum
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankData_Tables_of_window
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankLevels_candidates_nonempty
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightSharedReportingLevels
end ThreeSum.LightSharedReportingLevels
namespace ThreeSum.LightSignedLeafBatch
end ThreeSum.LightSignedLeafBatch
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightSwitch
end ThreeSum.LightSwitch
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.ReportingHostRelocation
end ThreeSum.ReportingHostRelocation
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.SharedReportingBankData
end ThreeSum.SharedReportingBankData
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614
end ThreeSum1960614
namespace ThreeSum1960614.LightQuarticSwitch
end ThreeSum1960614.LightQuarticSwitch
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels
end ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels
namespace ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch
end ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightSwitch
end ThreeSum1960614.Machine.ThreeSum.LightSwitch
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaCell
end ThreeSum1960614.Machine.ThreeSum.LightZetaCell
namespace ThreeSum1960614.Machine.ThreeSum.MaskDecode
end ThreeSum1960614.Machine.ThreeSum.MaskDecode
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
end ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum1960614
end ThreeSum1960614.Machine.ThreeSum1960614
namespace ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch
end ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch

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

/-- A procedure of a program is a procedure, with the same number, of the program with more
procedures appended. -/
theorem getElem?_append_of_eq_some {P : _root_.ThreeSum1960614.Machine.Light.Program} {p : ℕ} {body : _root_.ThreeSum1960614.Machine.Light.Stmt} (h : P[p]? = some body)
    (R : _root_.ThreeSum1960614.Machine.Light.Program) : (P ++ R)[p]? = some body := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h





/-- A run stays a run when procedures are appended to the program. -/
theorem Exec.append {s : _root_.ThreeSum1960614.Machine.Light.Stmt} {σ σ' : _root_.ThreeSum1960614.Machine.Light.State} {c : ℕ} (h : _root_.ThreeSum1960614.Machine.Light.Exec lim P d s σ σ' c) (R : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Exec lim (P ++ R) d s σ σ' c := by
  induction h with
  | skip => exact _root_.ThreeSum1960614.Machine.Light.Exec.skip
  | set h => exact _root_.ThreeSum1960614.Machine.Light.Exec.set h
  | store h₁ h₂ h₃ => exact _root_.ThreeSum1960614.Machine.Light.Exec.store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.call h₁ (_root_.ThreeSum1960614.Machine.Light.getElem?_append_of_eq_some h₂ R) h₃ ih

/-! ## The rules -/





/-- What is proved about a program holds for the program with more procedures appended. -/
theorem Ends.append {s σ T Q} (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d s σ T Q) (R : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim (P ++ R) d s σ T Q := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he.append R, hc, hq⟩























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









/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}















/-! ## The tactics -/











end Light

end

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







/-- A specification holds for the program with more procedures appended. -/
theorem Meets.append (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (P' : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim (P ++ P') p d vals μ T R := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, _root_.ThreeSum1960614.Machine.Light.getElem?_append_of_eq_some hp P', he.append P'⟩

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
The actual quartic integer test and its Light-language execution contract.
The finite scan and proof structure adapt the pinned Apache-2.0 source
Submission/ThreeSum/LightSwitch{,Bounds}.lean, commit
2b639655e07421b9ac743de9090459bab473a7c0.
The coefficients, powers and resource allowances below are changed to
the exact expansion-232 degree-four comparison in PROOF.md, Section 4.2.
-/

namespace ThreeSum1960614.LightQuarticSwitch
open _root_.ThreeSum1960614.LightQuarticSwitch


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000

















@[simp] theorem mem_candidates {J j r q : ℕ} :
    q ∈ _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.candidates J j r ↔ q ≤ r/2 ∧ _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.accepts J j r q := by
  simp [_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.candidates, Nat.lt_succ_iff]

theorem index_mem {J j r : ℕ} (h : (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.candidates J j r).Nonempty) :
    _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.index J j r ∈ _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.candidates J j r := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.index, dif_pos h]
  exact Finset.min'_mem _ _







theorem index_le_residual {J j r : ℕ} (hne : (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.candidates J j r).Nonempty) :
    _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.index J j r ≤ r :=
  (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.mem_candidates.mp (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.index_mem hne)).1.trans (Nat.div_le_self _ _)









variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {μ : ℕ→ℤ} {J j r q d : ℕ}













end ThreeSum1960614.LightQuarticSwitch

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact relocation of closed verified procedure libraries

Every procedure call is shifted by the same list offset. The structural
execution proof preserves the exact initial/final states, runtime, memory
addresses, values, and depth budget. It permits composition of independently
verified fixed programs without assuming a new implementation contract.
-/

namespace ThreeSum.ReportingHostRelocation
open _root_.ThreeSum.ReportingHostRelocation


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light





theorem lookup {P : _root_.ThreeSum1960614.Machine.Light.Program} {p : ℕ} {body : _root_.ThreeSum1960614.Machine.Light.Stmt} (h : P[p]? = some body) (prefixProgram : _root_.ThreeSum1960614.Machine.Light.Program) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program prefixProgram P)[prefixProgram.length+p]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate prefixProgram.length body) := by
  apply _root_.ThreeSum1960614.Machine.Light.getElem?_append_length_add
  rw [List.getElem?_map,h]
  rfl

theorem exec {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {s : _root_.ThreeSum1960614.Machine.Light.Stmt} {σ σ' : _root_.ThreeSum1960614.Machine.Light.State} {c : ℕ}
    (h : _root_.ThreeSum1960614.Machine.Light.Exec lim P d s σ σ' c) (prefixProgram : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Exec lim (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program prefixProgram P) d (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate prefixProgram.length s) σ σ' c := by
  induction h with
  | skip => exact _root_.ThreeSum1960614.Machine.Light.Exec.skip
  | set h => exact _root_.ThreeSum1960614.Machine.Light.Exec.set h
  | store h₁ h₂ h₃ => exact _root_.ThreeSum1960614.Machine.Light.Exec.store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.call h₁ (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.lookup h₂ prefixProgram) h₃ ih

theorem ends {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {s : _root_.ThreeSum1960614.Machine.Light.Stmt} {σ : _root_.ThreeSum1960614.Machine.Light.State} {T : ℕ} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}
    (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d s σ T Q) (prefixProgram : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program prefixProgram P) d (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate prefixProgram.length s) σ T Q := by
  obtain ⟨σ',c,he,hc,hq⟩ := h
  exact ⟨σ',c,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.exec he prefixProgram,hc,hq⟩

theorem meets {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {p d : ℕ} {vals : List ℤ} {μ : ℕ → ℤ}
    {T : ℕ} {R : ℤ → (ℕ → ℤ) → Prop} (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (prefixProgram : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program prefixProgram P) (prefixProgram.length+p) d vals μ T R := by
  obtain ⟨body,hbody,he⟩ := h
  exact ⟨_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate prefixProgram.length body,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.lookup hbody prefixProgram,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.ends he prefixProgram⟩

end ThreeSum.ReportingHostRelocation

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual complete shared prefix catalog from the original source tables

A single closed program constructs every aligned prefix-mask pair, reads its
computed count header, and builds all local suffix box tables. The original
record order is exact; no supplied enumeration, count, or table pointer is
used as an algorithmic oracle.
-/

namespace ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingPrefixCatalog


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}











theorem count_pos (h k : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k := by
  exact Nat.pow_pos (Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega)))







end ThreeSum.LightReportingPrefixCatalog

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! Compatibility interface consumed by the full reporting driver.
It delegates to the proved degree-four Light procedure. No cubic test or
separate callback implementation remains in this execution path. -/

namespace ThreeSum.LightSwitch
open _root_.ThreeSum.LightSwitch

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light










theorem index_le_residual {J j r : ℕ} (hne : (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates J j r).Nonempty) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex J j r ≤ r :=
  _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.index_le_residual hne



theorem meets {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {μ : ℕ→ℤ} {J j r d p : ℕ}
    (hp : P[p]?=some _root_.ThreeSum1960614.Machine.ThreeSum.LightSwitch.body) (hj : j ≤ J) (hne : (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates J j r).Nonempty)
    (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightSwitch.word J r : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [J,j,r] μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightSwitch.time r)
      (fun result ν => result=(_root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex J j r : ℤ) ∧ ν=μ) := by
  exact _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.meets hp hj hne hword

theorem program_meets {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ→ℤ} {J j r d : ℕ}
    (hj : j ≤ J) (hne : (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates J j r).Nonempty)
    (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightSwitch.word J r : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightSwitch.program 0 d [J,j,r] μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightSwitch.time r)
      (fun result ν => result=(_root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex J j r : ℤ) ∧ ν=μ) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightSwitch.meets rfl hj hne hword



end ThreeSum.LightSwitch

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact compact layout for a shared reporting catalog cell

The local pair and prefix counts are retained exactly. Each cell reserves
the two prefix arrays, its pointer row, all suffix boxes, the sorted index,
and the polynomial scratch used by the existing constructor. Layout sums
are later computed by the bank setup loop.
-/

namespace ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum.SharedReportingBankLayout


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog

set_option maxHeartbeats 1400000
set_option maxRecDepth 9000



























theorem ordered (base h J k boxCut : ℕ) :
    base ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairL base h ∧ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairL base h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairR base h ∧ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairR base h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageL base h ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageL base h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageR base h k ∧ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageR base h k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers base h k ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers base h k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes base h k ∧ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes base h k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks base h J k boxCut ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks base h J k boxCut ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work base h J k boxCut ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work base h J k boxCut ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish base h J k boxCut := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageR,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageL,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairR,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairL]
  omega

theorem finish_add (base h J k boxCut : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish base h J k boxCut=base+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.cellSize h J k boxCut := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.cellSize _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageR _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageL _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairR _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairL
  omega



theorem index_end (base h J k boxCut : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.index base h J k boxCut+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work base h J k boxCut := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.index _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work
  omega



theorem pair_scratch (base h J k boxCut : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work base h J k boxCut+2*(464*h)+2 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish base h J k boxCut := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth
  omega

theorem table_scratch (base h J k boxCut : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work base h J k boxCut+1+_root_.ThreeSum.LightPascal.tableSize (J*(464*h))+(J*(464*h)+1) ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish base h J k boxCut := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth
  omega









theorem levelOffset_step (h J : ℕ) (boxCut : ℕ → ℕ) (k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.levelOffset h J boxCut k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.levelOffset h J boxCut (k+1) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.levelOffset]
  omega

theorem levelOffset_mono (h J : ℕ) (boxCut : ℕ → ℕ) : Monotone (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.levelOffset h J boxCut) :=
  monotone_nat_of_le_succ (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.levelOffset_step h J boxCut)

theorem finish_level (base h J k : ℕ) (boxCut : ℕ → ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish (base+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.levelOffset h J boxCut k) h J k (boxCut k)=
      base+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.levelOffset h J boxCut (k+1) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish_add,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.levelOffset]
  omega

end ThreeSum.SharedReportingBankLayout

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Retain earlier shared catalogs while appending a later metadata record -/

namespace ThreeSum.SharedReportingBankData
open _root_.ThreeSum.SharedReportingBankData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData



theorem Entry.of_later {h J k record nextRecord low bound : ℕ} {μ ν : ℕ → ℤ}
    {D : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog} {hk : k ≤ J} {f g : Finset (Fin (J*(464*h))) → ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData.Entry μ record D hk f g) (heq : _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν bound nextRecord 5)
    (hrecord : record+5 ≤ nextRecord) (hnext : nextRecord+5 ≤ low)
    (hlow : low ≤ bound) (hindexLow : low ≤ D.indexBase)
    (hptrLow : low ≤ D.ptrBase) (hboxLow : low ≤ D.boxBase)
    (hindex : D.indexBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤ bound) (hptr : D.ptrBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤ bound)
    (hbox : D.boxBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k*_root_.ThreeSum.LightReportingSuffixCatalog.stride ((J-k)*(464*h)) D.boxCut ≤ bound) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData.Entry ν record D hk f g := by
  refine ⟨?_,H.tables.of_window (fun a ha hb => heq a ⟨hb,Or.inr (by omega)⟩)
    hindexLow hptrLow hboxLow hindex hptr hbox⟩
  intro i hi
  have hi' : i < 5 := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog.record,List.length_map,List.length_cons,List.length_nil] using hi
  exact (heq _ ⟨by omega,Or.inl (by omega)⟩).trans (H.header i hi)

end ThreeSum.SharedReportingBankData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact level layout and retention for one shared source pair -/

namespace ThreeSum.SharedReportingBankLevels
open _root_.ThreeSum.SharedReportingBankLevels


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData

set_option maxHeartbeats 1400000










theorem level_le {J k : ℕ} (hk : k ≤ _root_.ThreeSum.LightSwitchDepth.depth J) : k ≤ J := by
  have hh := Nat.div_mul_le_self (13*J) 20
  unfold _root_.ThreeSum.LightSwitchDepth.depth at hk
  omega



theorem switch_le {h J k : ℕ} (hk : k ≤ _root_.ThreeSum.LightSwitchDepth.depth J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.switch h J k ≤ _root_.ThreeSum.SharedReportingBankLevels.residual h J k :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightSwitch.index_le_residual (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.candidates_nonempty hk)

theorem boxCut_le (h J k : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J k ≤ _root_.ThreeSum.SharedReportingBankLevels.residual h J k := Nat.sub_le _ _

theorem residual_le_width (h J k : ℕ) : _root_.ThreeSum.SharedReportingBankLevels.residual h J k ≤ (J-k)*(464*h) := by
  unfold _root_.ThreeSum.SharedReportingBankLevels.residual
  nlinarith

theorem pre_cut {h J k : ℕ} (hk : k ≤ J) : k*h+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J k ≤ 2*h*J := by
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut_le h J k
  have hd := Nat.sub_add_cancel hk
  unfold _root_.ThreeSum.SharedReportingBankLevels.residual at hc
  nlinarith

theorem count_zero (h : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h 0=1 := by simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count]
theorem count_succ (h k : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h (k+1)=_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth,pow_succ]
theorem span_zero (h : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.prefixSpan h 0=2 := by
  simp [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.prefixSpan,_root_.ThreeSum.LightRadixKeys.offset,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count]
theorem span_succ (h k : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.prefixSpan h (k+1)=_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.prefixSpan h k+1+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h (k+1) := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.prefixSpan
  rw [_root_.ThreeSum.LightRadixKeys.offset]
  change _root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h) k+1+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k+1+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h (k+1)=_
  omega

theorem count_mono (h : ℕ) : Monotone (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h) := by
  intro i j hij
  exact Nat.pow_le_pow_right (by
    have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count_pos h 1
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count,pow_one] using hh) hij

theorem span_mono (h : ℕ) : Monotone (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.prefixSpan h) :=
  monotone_nat_of_le_succ (fun k => by rw [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.span_succ]; omega)

theorem baseAt_zero (base h J : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J 0=base := rfl
theorem baseAt_mono (base h J : ℕ) : Monotone (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J) := by
  intro i j hij
  exact Nat.add_le_add_left (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.levelOffset_mono h J (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J) hij) base

theorem finish_baseAt (base h J k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J k) h J k (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J k)=_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J (k+1) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish_level base h J k (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J)

theorem catalog_low (base h J k : ℕ) :
    base ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalogAt base h J k).indexBase ∧
    base ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalogAt base h J k).ptrBase ∧
    base ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalogAt base h J k).boxBase := by
  have ho := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.ordered (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J k) h J k (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J k)
  have hb : base ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J k := Nat.le_add_right _ _
  dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalogAt,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.catalog,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.index]
  omega

theorem catalog_end (base h J k : ℕ) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalogAt base h J k).indexBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J (k+1) ∧
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalogAt base h J k).ptrBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J (k+1) ∧
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalogAt base h J k).boxBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k*
      _root_.ThreeSum.LightReportingSuffixCatalog.stride ((J-k)*(464*h)) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J k) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J (k+1) := by
  have ho := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.ordered (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J k) h J k (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J k)
  have hi := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.index_end (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J k) h J k (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J k)
  have hp : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J k) h k+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k=_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J k) h k := rfl
  have hm : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J k) h k+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k*
      _root_.ThreeSum.LightReportingSuffixCatalog.stride ((J-k)*(464*h)) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J k)=_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J k) h J k (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J k) := rfl
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.finish_baseAt]
  dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalogAt,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.catalog]
  omega

theorem Built.empty (μ : ℕ → ℤ) (record base h J : ℕ)
    (f g : Finset (Fin (J*(464*h))) → ℤ) : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.Built μ record base h J 0 f g := by
  intro k hk
  omega

theorem Built.append {μ ν : ℕ → ℤ} {record base h J i : ℕ}
    {f g : Finset (Fin (J*(464*h))) → ℤ} (H : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.Built μ record base h J i f g)
    (hi : i ≤ J)
    (Hnew : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData.Entry ν (record+5*i) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalogAt base h J i) hi f g)
    (hkeep : _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J i) (record+5*i) 5)
    (hrecord : record+5*i+5 ≤ base) : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.Built ν record base h J (i+1) f g := by
  intro j hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · obtain ⟨hjJ,Hj⟩ := H j hj
    have hlow := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalog_low base h J j
    have hend := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalog_end base h J j
    have hbefore := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt_mono base h J (show j+1 ≤ i by omega)
    refine ⟨hjJ,Hj.of_later hkeep (by omega) hrecord
      (Nat.le_add_right _ _) hlow.1 hlow.2.1 hlow.2.2
      (hend.1.trans hbefore) (hend.2.1.trans hbefore) (hend.2.2.trans hbefore)⟩
  · exact ⟨hi,Hnew⟩

end ThreeSum.SharedReportingBankLevels

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
open _root_.ThreeSum.SharedReportingBankLevels
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels
set_option maxHeartbeats 3000000
set_option maxRecDepth 14000
section

theorem ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels.program_meets__implementation_9b8c41ba22 {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ → ℤ}
    {record base h J K baseL baseR cellL cellR B D d : ℕ}
    (f g : Finset (Fin (J*(464*h))) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hK : K ≤ _root_.ThreeSum.LightSwitchDepth.depth J+1)
    (hrecords : record+5*K ≤ base)
    (hcellL : cellL < record) (hcellR : cellR < record)
    (hdataL : baseL+(J*(464*h)+1)*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) (2*h*J) ≤ record)
    (hdataR : baseR+(J*(464*h)+1)*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) (2*h*J) ≤ record)
    (R : _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels.Resources lim base h J K B D d)
    (hf : ∀ S, S.card ≤ 2*h*J → |f S| ≤ B)
    (hg : ∀ S, S.card ≤ 2*h*J → |g S| ≤ D)
    (hleftRead : μ cellL=(baseL : ℤ)) (hrightRead : μ cellR=(baseR : ℤ))
    (hstoredL : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseL (2*h*J) f (J*(464*h)))
    (hstoredR : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseR (2*h*J) g (J*(464*h))) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels.program 64 d
      [h,J,K,cellL,cellR,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localChoose h,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h,record,base] μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels.time h J K)
      (fun result ν => result=(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J K : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.Built ν record base h J K f g ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν record ∧ _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν base record (5*K)) := by
  have hstate := R.state
  have hspace := R.space
  have hdepth := R.widthDepth
  have hbase : base ≤ lim.space := (Nat.le_add_right _ _).trans hspace
  have hKWord : (K : ℤ) ≤ lim.word := by omega
  have hJWord : (J : ℤ) ≤ lim.word := by omega
  have hconstants : (464 : ℤ) ≤ lim.word := by omega
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 64) (by rfl : program[64]?=some (body 63 62))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels.body _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels.time
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (2 : ℕ) ?_ ?_ ?_
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (base : ℕ) ?_ ?_ ?_
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
  refine _root_.ThreeSum1960614.Machine.Light.Ends.pieceThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLoop.forSum
    (T := (∑ i ∈ Finset.range K, (_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels.roundTime h J i+8))+6)
    (Q := _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels.Inv μ record base h J K cellL cellR K f g)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels.Inv μ record base h J K cellL cellR · f g) K (_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels.roundTime h J)
    ?start ?round ?done ?bound hKWord (by
      simp only [_root_.ThreeSum1960614.Machine.Light.Expr.cost]
      have hs : (∑ i ∈ Finset.range K, (1+_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels.roundTime h J i+7))=
          ∑ i ∈ Finset.range K, (_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels.roundTime h J i+8) := by
        apply Finset.sum_congr rfl
        intro i hi
        omega
      omega)) ?finish
  case start =>
    refine ⟨0,0,0,μ,?_,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.Built.empty _ _ _ _ _ _ _,_root_.ThreeSum1960614.Machine.Light.SameOn.refl,fun _ _ => rfl⟩
    simp only [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.count_zero,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.span_zero,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt_zero]
    simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]
    exact (_root_.ThreeSum1960614.Machine.Light.frame_append_zeros [h,J,K,cellL,cellR,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localChoose h,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h,record,base,1,2,base,0] 3).symm
  case round =>
    rintro i _ hi _ ⟨r,t,cut,ν,rfl,built,kept,keptBlock⟩
    have hiDepth : i ≤ _root_.ThreeSum.LightSwitchDepth.depth J := by omega
    have hiJ := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.level_le hiDepth
    have hnext := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt_mono base h J (show i+1 ≤ K by omega)
    have hcellSpace : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J i) h J i (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J i) ≤ lim.space := by
      rw [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.finish_baseAt]
      exact hnext.trans hspace
    have hbefore := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt_mono base h J (show i ≤ K by omega)
    have hcurrent : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J i ≤ lim.space := hbefore.trans hspace
    have hlocalSpace := (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pair_scratch (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J i) h J i (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J i)).trans hcellSpace
    have hwidthSpace := (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.table_scratch (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J i) h J i (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J i)).trans hcellSpace
    have hW : J*(464*h) ≤ lim.space := by omega
    have hL : 464*h ≤ lim.space := by omega
    have hV : (J-i)*(464*h) ≤ J*(464*h) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    have hrV := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.residual_le_width h J i
    have hrNat : _root_.ThreeSum.SharedReportingBankLevels.residual h J i ≤ lim.space := by omega
    have hrWord : (2 : ℤ)*(h : ℤ)*((J : ℤ)-(i : ℤ)) ≤ lim.word := by
      simpa only [_root_.ThreeSum.SharedReportingBankLevels.residual,Nat.cast_mul,Nat.cast_sub hiJ,Nat.cast_ofNat] using
        (Int.ofNat_le.mpr hrNat).trans hw
    have hrNZ : (0 : ℤ) ≤ (2 : ℤ)*(h : ℤ)*((J : ℤ)-(i : ℤ)) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr (Int.ofNat_le.mpr hiJ))
    have hN := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.count_mono h (show i+1 ≤ K by omega)
    have hspan := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.span_mono h (show i+1 ≤ K by omega)
    have hprod : (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h i : ℤ)*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h : ℤ)=(_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h (i+1) : ℤ) := by
      rw [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.count_succ,Nat.cast_mul]
    have hprodNZ : (0 : ℤ) ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h i : ℤ)*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h : ℤ) := by positivity
    have hspanEq := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.span_succ h i
    have hrecord : record+5*i+5 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J i := by
      have hb : base ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J i := Nat.le_add_right _ _
      omega
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels.roundTime
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SharedReportingBankLevels.residual h J i : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.SharedReportingBankLevels.residual, Nat.cast_sub hiJ]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum.SharedReportingBankLevels.residual, Nat.cast_sub hiJ] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.SharedReportingBankLevels.residual, Nat.cast_sub hiJ] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    have hs := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.meets
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightSwitch.program_meets (μ := ν) (d := d+1) hiJ (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.candidates_nonempty hiDepth) (R.switch i hi))
      _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCell.program).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels.body 63 62]
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
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.SharedReportingBankLevels.residual]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum.SharedReportingBankLevels.residual] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.SharedReportingBankLevels.residual] <;> omega)
       on_goal -1 => (rintro actual νt ⟨hactual, hmem⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    subst νt
    have hswitch := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.switch_le (h := h) hiDepth
    change _root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex J i (_root_.ThreeSum.SharedReportingBankLevels.residual h J i) ≤ _root_.ThreeSum.SharedReportingBankLevels.residual h J i at hswitch
    have htWord : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.switch h J i : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (hswitch.trans hrNat)).trans hw
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J i : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.switch, hactual]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.switch, hactual] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.switch, hactual] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    have hsourceL : _root_.ThreeSum.LightZetaStages.StoredThrough ν baseL (2*h*J) f (J*(464*h)) :=
      _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch.storedThrough_of_on hstoredL
        (by intro a _ ha; exact kept a (by omega))
    have hsourceR : _root_.ThreeSum.LightZetaStages.StoredThrough ν baseR (2*h*J) g (J*(464*h)) :=
      _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch.storedThrough_of_on hstoredR
        (by intro a _ ha; exact kept a (by omega))
    have hreadL : ν cellL=(baseL : ℤ) := (kept cellL hcellL).trans hleftRead
    have hreadR : ν cellR=(baseR : ℤ) := (kept cellR hcellR).trans hrightRead
    have hc := ((_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCell.program_meets (μ := ν) (d := d+1)
      (k := i) (boxCut := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J i) (baseL := baseL) (baseR := baseR)
      (cellL := cellL) (cellR := cellR) (free := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J i) (rec := record+5*i)
      (B := B) (D := D) (t := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.switch h J i) hiJ f g hw hconstants hJWord
      ((_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut_le h J i).trans hrV) (by omega) (by omega) (by omega) (by omega) hrecord
      hcellSpace R.powers (R.keys i hi) R.width (R.index i hi) (R.values i hi) htWord
      (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.pre_cut hiJ) hf hg hreadL hreadR hsourceL hsourceR
      (by have hh := R.pairDepth; omega) (by have hh := R.widthDepth; omega)
      (by have hh := R.sortDepth i hi; omega)).append
        (_root_.ThreeSum1960614.Machine.ThreeSum.LightSwitch.program.map (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCell.program.length))).append
          [_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels.body 63 62]
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
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hactual, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.switch]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hactual, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.switch] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hactual, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.switch] <;> omega)
       on_goal -1 => (rintro next ν₁ ⟨hnextFree, hentry, _, _, hkeepCell⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h (i + 1) : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.count_succ]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.count_succ] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.count_succ] <;> omega)
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
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.prefixSpan h (i + 1) : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.span_succ]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.span_succ] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.span_succ] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    refine ⟨by simp,_root_.ThreeSum.SharedReportingBankLevels.residual h J i,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.switch h J i,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J i,ν₁,?_,?_,?_,?_⟩
    · simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal,hnextFree,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.finish_baseAt,hactual,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.switch]
    · exact built.append hiJ hentry hkeepCell (by omega)
    · intro a ha
      exact (hkeepCell a ⟨by omega,Or.inl (by omega)⟩).trans (kept a ha)
    · intro a ⟨ha,houtside⟩
      have hb : base ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J i := Nat.le_add_right _ _
      exact (hkeepCell a ⟨by omega,by rcases houtside with h | h <;> omega⟩).trans
        (keptBlock a ⟨ha,houtside⟩)
  case done =>
    rintro _ _ ⟨r,t,cut,ν,rfl,built,kept,keptBlock⟩
    exact ⟨r,t,cut,ν,rfl,built,kept,keptBlock⟩
  case bound =>
    rintro i _ _ _ ⟨r,t,cut,ν,rfl,_,_,_⟩
    (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
  case finish =>
    rintro _ ⟨r,t,cut,ν,rfl,built,kept,keptBlock⟩
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J K : ℕ) ?_ ?_ ?_
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
    exact ⟨rfl,built,kept,keptBlock⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels.program_meets__implementation_9b8c41ba22) := (@ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels.program_meets__implementation_9b8c41ba22)

#print axioms solution
