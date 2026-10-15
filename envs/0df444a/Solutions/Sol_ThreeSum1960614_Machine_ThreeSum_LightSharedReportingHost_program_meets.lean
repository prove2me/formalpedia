-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightSharedReportingHost.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:52:25.74063+00:00
-- url     : https://prove2.me/submissions/06d2319b-6165-4209-b448-3e85c9e71567

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
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
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
import Definitions.Def_ThreeSum1960614_Machine_Bundle036
import Definitions.Def_ThreeSum1960614_Machine_Bundle037
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
import Definitions.Def_ThreeSum1962Source_Bundle16
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
import Mathlib.Algebra.GCDMonoid.Nat
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
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
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
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
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
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.DeriveFintype
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSharedReportingBank_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSharedReportingCounts_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSmallDivide_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SourceBandBankData_Stored_of_kept
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightSharedReportingHost
end ThreeSum.LightSharedReportingHost
namespace ThreeSum.LightSwitchDepth
end ThreeSum.LightSwitchDepth
namespace ThreeSum.ReportingHostQueryBounds
end ThreeSum.ReportingHostQueryBounds
namespace ThreeSum.ReportingHostRelocation
end ThreeSum.ReportingHostRelocation
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.SharedReportingBankData
end ThreeSum.SharedReportingBankData
namespace ThreeSum.SharedReportingBankHeader
end ThreeSum.SharedReportingBankHeader
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SharedReportingBankRows
end ThreeSum.SharedReportingBankRows
namespace ThreeSum.SourceBandBankData
end ThreeSum.SourceBandBankData
namespace ThreeSum.SourceBandLayout
end ThreeSum.SourceBandLayout
namespace ThreeSum.SourceBandPairData
end ThreeSum.SourceBandPairData
namespace ThreeSum.SourceBandPairSlices
end ThreeSum.SourceBandPairSlices
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightSharedReportingHost
end ThreeSum1960614.Machine.ThreeSum.LightSharedReportingHost
namespace ThreeSum1960614.Machine.ThreeSum.LightSwitchDepth
end ThreeSum1960614.Machine.ThreeSum.LightSwitchDepth
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostQueryBounds
end ThreeSum1960614.Machine.ThreeSum.ReportingHostQueryBounds
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
end ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandBankData
end ThreeSum1960614.Machine.ThreeSum.SourceBandBankData
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout
end ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandLayout
end ThreeSum1960614.Machine.ThreeSum.SourceBandLayout
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandPairData
end ThreeSum1960614.Machine.ThreeSum.SourceBandPairData
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandPairSlices
end ThreeSum1960614.Machine.ThreeSum.SourceBandPairSlices
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













/-- Reading a cell of a segment, with a default value for the list. -/
theorem Seg.getD (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) {i : ℕ} (hi : i < l.length) (d : ℤ) : μ (a + i) = l.getD i d := by
  rw [h i hi, List.getD_eq_getElem _ _ hi]

































































end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual computation of the terminal reporting depth -/

namespace ThreeSum.LightSwitchDepth
open _root_.ThreeSum.LightSwitchDepth


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light








variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {μ : ℕ→ℤ} {J d : ℕ}

theorem meets {p pDiv : ℕ} (hp : P[p]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSwitchDepth.body pDiv))
    (hdiv : P[pDiv]?=some _root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.body)
    (hword : (_root_.ThreeSum.LightSwitchDepth.word J : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [J] μ (_root_.ThreeSum.LightSwitchDepth.time J)
      (fun result ν => result=(_root_.ThreeSum.LightSwitchDepth.depth J : ℤ) ∧ ν=μ) := by
  unfold _root_.ThreeSum.LightSwitchDepth.word at hword
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hp
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSwitchDepth.body _root_.ThreeSum.LightSwitchDepth.time
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.meets (d := d+1) (a := 13*J) (b := 20) hdiv μ hword
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
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightSwitchDepth.word, _root_.ThreeSum.LightSmallDivide.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightSwitchDepth.word, _root_.ThreeSum.LightSmallDivide.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightSwitchDepth.word, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
     on_goal -1 => (rintro result ν ⟨hresult, rfl⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightSwitchDepth.depth J) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightSwitchDepth.depth, _root_.ThreeSum.LightSwitchDepth.word, _root_.ThreeSum.LightSmallDivide.time, hresult]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightSwitchDepth.depth, _root_.ThreeSum.LightSwitchDepth.word, _root_.ThreeSum.LightSmallDivide.time, hresult] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightSwitchDepth.depth, _root_.ThreeSum.LightSwitchDepth.word, _root_.ThreeSum.LightSmallDivide.time, hresult] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  exact ⟨rfl,rfl⟩



theorem program_meets (hword : (_root_.ThreeSum.LightSwitchDepth.word J : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightSwitchDepth.program 0 d [J] μ (_root_.ThreeSum.LightSwitchDepth.time J)
      (fun result ν => result=(_root_.ThreeSum.LightSwitchDepth.depth J : ℤ) ∧ ν=μ) := _root_.ThreeSum1960614.Machine.ThreeSum.LightSwitchDepth.meets rfl rfl hword hd





end ThreeSum.LightSwitchDepth

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Output bounds and stored-table preservation for actual query batching -/

namespace ThreeSum.ReportingHostQueryBounds
open _root_.ThreeSum.ReportingHostQueryBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open scoped _root_.BigOperators







theorem boxStored_of_on {W cut base : ℕ} {μ μ' : ℕ → ℤ} {f : Finset (Fin W) → ℤ}
    (h : _root_.ThreeSum.LightBoxStages.StoredThrough μ base cut f W)
    (hkeep : ∀ i, base ≤ i → i < base+(W+1)*_root_.ThreeSum.SubsetAddress.downsetCap W cut → μ' i = μ i) :
    _root_.ThreeSum.LightBoxStages.StoredThrough μ' base cut f W := by
  intro j hj S hS
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.subsetRank_lt hS
  have hm := Nat.mul_le_mul_right (_root_.ThreeSum.SubsetAddress.downsetCap W cut) (Nat.succ_le_succ hj)
  simp only [Nat.succ_mul] at hm
  have he := hkeep (base+j*_root_.ThreeSum.SubsetAddress.downsetCap W cut+_root_.ThreeSum.SubsetAddress.subsetRank S) (by omega) (by
    simp only [Nat.succ_mul]
    omega)
  exact he.trans (h j hj S hS)

end ThreeSum.ReportingHostQueryBounds

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

/-! # Padded histogram selection for independently chosen original bands -/

namespace ThreeSum.SourceBandPairSlices
open _root_.ThreeSum.SourceBandPairSlices


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.SourceBandLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout
open _root_.ThreeSum.SourceBandPairData
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData



















theorem heads_read {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g p m : ℕ} {shift : ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.Stored μ fL fR base NL NR g p m shift) :
    μ base=(_root_.ThreeSum.SourceBandPairData.leftBase base : ℤ) ∧ μ (base+1)=(_root_.ThreeSum.BandPartition.size NL g : ℤ) ∧
    μ (base+2)=(_root_.ThreeSum.SourceBandPairData.rightBase base NL g m : ℤ) ∧ μ (base+3)=(_root_.ThreeSum.BandPartition.size NR g : ℤ) ∧
    μ (base+4)=(_root_.ThreeSum.SourceBandPairData.zeroBase base NL NR g m : ℤ) ∧ μ (base+5)=(_root_.ThreeSum.SourceBandPairData.next base NL NR g m : ℤ) ∧
    μ (base+6)=(NL : ℤ) ∧ μ (base+7)=(NR : ℤ) := by
  exact ⟨by simpa [_root_.ThreeSum.SourceBandPairData.header] using H.heads.getD (i := 0) (by simp [_root_.ThreeSum.SourceBandPairData.header]) 0,
    by simpa [_root_.ThreeSum.SourceBandPairData.header] using H.heads.getD (i := 1) (by simp [_root_.ThreeSum.SourceBandPairData.header]) 0,
    by simpa [_root_.ThreeSum.SourceBandPairData.header] using H.heads.getD (i := 2) (by simp [_root_.ThreeSum.SourceBandPairData.header]) 0,
    by simpa [_root_.ThreeSum.SourceBandPairData.header] using H.heads.getD (i := 3) (by simp [_root_.ThreeSum.SourceBandPairData.header]) 0,
    by simpa [_root_.ThreeSum.SourceBandPairData.header] using H.heads.getD (i := 4) (by simp [_root_.ThreeSum.SourceBandPairData.header]) 0,
    by simpa [_root_.ThreeSum.SourceBandPairData.header] using H.heads.getD (i := 5) (by simp [_root_.ThreeSum.SourceBandPairData.header]) 0,
    by simpa [_root_.ThreeSum.SourceBandPairData.header] using H.heads.getD (i := 6) (by simp [_root_.ThreeSum.SourceBandPairData.header]) 0,
    by simpa [_root_.ThreeSum.SourceBandPairData.header] using H.heads.getD (i := 7) (by simp [_root_.ThreeSum.SourceBandPairData.header]) 0⟩

end ThreeSum.SourceBandPairSlices

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact retained cells of one shared reporting catalog -/

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

set_option maxHeartbeats 1500000
set_option maxRecDepth 9000





theorem Tables.of_after {h J k low : ℕ} {μ ν : ℕ → ℤ} {D : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog} {hk : k ≤ J}
    {f g : Finset (Fin (J*(464*h))) → ℤ} (H : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData.Tables μ D hk f g)
    (heq : ∀ a, low ≤ a → ν a=μ a)
    (hindex : low ≤ D.indexBase) (hptr : low ≤ D.ptrBase) (hbox : low ≤ D.boxBase) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData.Tables ν D hk f g := by
  obtain ⟨S,hs,hperm,hsort⟩ := H.index
  refine ⟨⟨S,?_,hperm,hsort⟩,?_,?_⟩
  · intro i hi
    exact (heq _ (by omega)).trans (hs i hi)
  · intro i hi
    exact (heq _ (by omega)).trans (H.pointers i hi)
  · intro i hi
    exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostQueryBounds.boxStored_of_on (H.boxes i hi)
      (by intro a ha _; exact heq a (by omega))







end ThreeSum.SharedReportingBankData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Retained common-band source catalog with one occurrence table -/

namespace ThreeSum.SourceBandBankData
open _root_.ThreeSum.SourceBandBankData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords












theorem Stored.heads_read {μ : ℕ → ℤ} {fL fR : ℕ → ℤ}
    {base NL NR g h J cut occ : ℕ} {p shift : ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.Stored μ fL fR base NL NR g h J cut occ p shift) :
    μ base=(_root_.ThreeSum.SourceBandBankData.first base : ℤ) ∧ μ (base+1)=(_root_.ThreeSum.SourceBandPairSlices.count NL NR g : ℤ) ∧
    μ (base+2)=(_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span h J cut : ℤ) ∧ μ (base+3)=(_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.finish base NL NR g h J cut : ℤ) ∧
    μ (base+4)=(occ : ℤ) :=
  ⟨by simpa [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.header] using H.heads.getD (i := 0) (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.header]) 0,
    by simpa [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.header] using H.heads.getD (i := 1) (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.header]) 0,
    by simpa [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.header] using H.heads.getD (i := 2) (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.header]) 0,
    by simpa [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.header] using H.heads.getD (i := 3) (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.header]) 0,
    by simpa [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.header] using H.heads.getD (i := 4) (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.header]) 0⟩

end ThreeSum.SourceBandBankData

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



























end ThreeSum.SharedReportingBankLayout

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

























theorem catalog_low (base h J k : ℕ) :
    base ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalogAt base h J k).indexBase ∧
    base ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalogAt base h J k).ptrBase ∧
    base ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalogAt base h J k).boxBase := by
  have ho := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.ordered (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J k) h J k (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J k)
  have hb : base ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J k := Nat.le_add_right _ _
  dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalogAt,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.catalog,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.index]
  omega







end ThreeSum.SharedReportingBankLevels

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # A retained header for the complete shared reporting catalog bank -/

namespace ThreeSum.SharedReportingBankHeader
open _root_.ThreeSum.SharedReportingBankHeader


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.SharedReportingBankRows
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows
open _root_.ThreeSum.SharedReportingBankLevels
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData

set_option maxHeartbeats 1900000







theorem levels_pos (J : ℕ) : 0 < _root_.ThreeSum.SharedReportingBankHeader.levels J := by unfold _root_.ThreeSum.SharedReportingBankHeader.levels; omega
theorem records_le_payload (free h J NB NC g : ℕ) :
    _root_.ThreeSum.SharedReportingBankHeader.records free ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload free h J NB NC g := Nat.le_add_right _ _
theorem payload_le_finish (free h J NB NC g : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload free h J NB NC g ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish free h J NB NC g := Nat.le_add_right _ _


theorem levels_of_after {μ ν : ℕ → ℤ} {record base h J K low : ℕ}
    {f g : Finset (Fin (J*(464*h))) → ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.Built μ record base h J K f g) (heq : ∀ a, low ≤ a → ν a=μ a)
    (hrecord : low ≤ record) (hbase : low ≤ base) : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.Built ν record base h J K f g := by
  intro k hk
  obtain ⟨hkJ,Hk⟩ := H k hk
  have hlo := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalog_low base h J k
  refine ⟨hkJ,⟨?_,Hk.tables.of_after heq (hbase.trans hlo.1)
    (hbase.trans hlo.2.1) (hbase.trans hlo.2.2)⟩⟩
  intro i hi
  exact (heq _ (by omega)).trans (Hk.header i hi)

theorem done_of_after {μ ν : ℕ → ℤ} {record base h J K NB NC g processed low : ℕ}
    {fB fC : ℕ → ℤ} {p shift : ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.Done μ record base h J K NB NC g processed fB fC p shift)
    (heq : ∀ a, low ≤ a → ν a=μ a) (hrecord : low ≤ record) (hbase : low ≤ base) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.Done ν record base h J K NB NC g processed fB fC p shift := by
  intro s hs i hi j hj hr
  exact _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.levels_of_after (H s hs i hi j hj hr) heq
    (hrecord.trans (Nat.le_add_right _ _)) (hbase.trans (Nat.le_add_right _ _))









end ThreeSum.SharedReportingBankHeader

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingHost

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum.SharedReportingBankRows
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows
open _root_.ThreeSum.SharedReportingBankHeader
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader
set_option maxHeartbeats 3900000
set_option maxRecDepth 16000
section

theorem ThreeSum1960614.Machine.ThreeSum.LightSharedReportingHost.program_meets__implementation_16b9b0f473 {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ → ℤ} {fB fC : ℕ → ℤ}
    {controls pairHeader bankHeader free NB NC g h J occ p m d : ℕ} {shift : ℤ}
    (Hcontrol : _root_.ThreeSum1960614.Machine.Light.Seg μ controls (_root_.ThreeSum1960614.Machine.ThreeSum.SourceControlLayout.values h J (2*h*J)))
    (Hpair : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.Stored μ fB fC pairHeader NB NC g p m shift)
    (Hbank : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.Stored μ fB fC bankHeader NB NC g h J (2*h*J) occ (p : ℤ) shift)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hcontrol : controls+3 ≤ free) (hpair : pairHeader+8 ≤ free)
    (hocc : occ+_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J*J ≤ bankHeader)
    (hsource : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.finish bankHeader NB NC g h J (2*h*J) ≤ free)
    (R : _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingHost.Resources lim free h J NB NC g d) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingHost.program 74 d [h,J,controls,pairHeader,bankHeader,free] μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingHost.time h J NB NC g)
      (fun result ν => result=(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish free h J NB NC g : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.Stored ν free h J NB NC g fB fC (p : ℤ) shift ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν free) := by
  have hfinish : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish free h J NB NC g ≤ lim.space := (le_max_right _ _).trans R.space
  have hpascal : _root_.ThreeSum.SharedReportingBankHeader.records free+_root_.ThreeSum.LightPascal.tableSize (464*h) ≤ lim.space :=
    (le_max_left _ _).trans R.space
  have hpayload : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload free h J NB NC g ≤ lim.space := (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload_le_finish _ _ _ _ _ _).trans hfinish
  have hrecords : _root_.ThreeSum.SharedReportingBankHeader.records free ≤ lim.space := (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.records_le_payload _ _ _ _ _ _).trans hpayload
  have hfree : free+9 ≤ lim.space := hrecords
  have hsourceStart : bankHeader+5 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.finish bankHeader NB NC g h J (2*h*J) :=
    Nat.le_add_right _ _
  have hctl := R.control
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingBank.controlWord at hctl
  have hconstants : (464 : ℤ) ≤ lim.word := by exact_mod_cast (show (464 : ℤ) ≤ lim.word by omega)
  have hchoose : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localChoose h ≤ 2^(464*h+1) :=
    (Nat.choose_le_two_pow (464*h) h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hdepth := R.depth
  have hdepthJ : _root_.ThreeSum.LightSwitchDepth.depth J ≤ J := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.level_le le_rfl
  have hspan := R.span
  have hpairs := R.pairs
  have hpow := R.powers
  have hdword := R.depthWord
  have hKword : ((5*_root_.ThreeSum.SharedReportingBankHeader.levels J : ℕ) : ℤ) ≤ lim.word := by
    apply (Int.ofNat_le.mpr (show 5*_root_.ThreeSum.SharedReportingBankHeader.levels J ≤ _root_.ThreeSum.LightSwitchDepth.word J by
      unfold _root_.ThreeSum.SharedReportingBankHeader.levels _root_.ThreeSum.LightSwitchDepth.depth _root_.ThreeSum.LightSwitchDepth.word
      omega)).trans R.depthWord
  have hPword : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.total h J NB NC g : ℤ) ≤ lim.word := by
    have hh := Nat.le_mul_of_pos_left (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.total h J NB NC g) (show 0 < 5*_root_.ThreeSum.SharedReportingBankHeader.levels J by
      have hk := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.levels_pos J
      omega)
    exact (Int.ofNat_le.mpr (show _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.total h J NB NC g ≤ lim.space by unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload at hpayload; omega)).trans hw
  have hpOne : (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J : ℤ)*(_root_.ThreeSum.BandPartition.size NB g : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (show _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J*_root_.ThreeSum.BandPartition.size NB g ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingBank.controlWord h J (_root_.ThreeSum.SharedReportingBankHeader.levels J) NB NC g by
      unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingBank.controlWord; omega)).trans R.control
  have hpOneNZ : (0 : ℤ) ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J : ℤ)*(_root_.ThreeSum.BandPartition.size NB g : ℤ) := by positivity
  have hpTwo : (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J : ℤ)*(_root_.ThreeSum.BandPartition.size NB g : ℤ)*
      (_root_.ThreeSum.BandPartition.size NC g : ℤ) ≤ lim.word := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.total,_root_.ThreeSum.SharedReportingBankRows.pairs,Nat.cast_mul] using hPword
  have hpTwoNZ : (0 : ℤ) ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J : ℤ)*(_root_.ThreeSum.BandPartition.size NB g : ℤ)*
      (_root_.ThreeSum.BandPartition.size NC g : ℤ) := by positivity
  have hmetaNZ : (0 : ℤ) ≤ 5*(_root_.ThreeSum.SharedReportingBankHeader.levels J : ℤ)*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.total h J NB NC g : ℤ) := by positivity
  have hmetaWord : 5*(_root_.ThreeSum.SharedReportingBankHeader.levels J : ℤ)*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.total h J NB NC g : ℤ) ≤ lim.word := by
    exact_mod_cast (show ((5*_root_.ThreeSum.SharedReportingBankHeader.levels J*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.total h J NB NC g : ℕ) : ℤ) ≤ lim.word from
      (Int.ofNat_le.mpr (show 5*_root_.ThreeSum.SharedReportingBankHeader.levels J*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.total h J NB NC g ≤ lim.space by unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload at hpayload; omega)).trans hw)
  have hpayloadWord : (_root_.ThreeSum.SharedReportingBankHeader.records free : ℤ)+5*(_root_.ThreeSum.SharedReportingBankHeader.levels J : ℤ)*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.total h J NB NC g : ℤ) ≤ lim.word := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using
      (Int.ofNat_le.mpr hpayload).trans hw
  have hreadS : μ (controls+1)=(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J : ℤ) := by
    simpa [_root_.ThreeSum1960614.Machine.ThreeSum.SourceControlLayout.values] using Hcontrol.getD (i := 1) (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.SourceControlLayout.values]) 0
  obtain ⟨_,hreadNB,_,hreadNC,_⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairSlices.heads_read Hpair
  obtain ⟨hreadFirst,_,hreadSpan,_⟩ := Hbank.heads_read
  have haS : ((controls : ℤ)+1).toNat=controls+1 := by omega
  have haB : ((pairHeader : ℤ)+1).toNat=pairHeader+1 := by omega
  have haC : ((pairHeader : ℤ)+3).toNat=pairHeader+3 := by omega
  have haSpan : ((bankHeader : ℤ)+2).toNat=bankHeader+2 := by omega
  have haH : ((free : ℤ)+7).toNat=free+7 := by omega
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 74) (by rfl : program[74]?=some (body 67 69 66))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingHost.body _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingHost.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadS, haS, _root_.ThreeSum.SharedReportingBankHeader.records]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hreadS, haS, _root_.ThreeSum.SharedReportingBankHeader.records] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadS, haS, _root_.ThreeSum.SharedReportingBankHeader.records] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.BandPartition.size NB g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadNB, haB, _root_.ThreeSum.SharedReportingBankHeader.records]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hreadNB, haB, _root_.ThreeSum.SharedReportingBankHeader.records] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadNB, haB, _root_.ThreeSum.SharedReportingBankHeader.records] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.BandPartition.size NC g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadNC, haC, _root_.ThreeSum.SharedReportingBankHeader.records]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hreadNC, haC, _root_.ThreeSum.SharedReportingBankHeader.records] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadNC, haC, _root_.ThreeSum.SharedReportingBankHeader.records] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SourceBandBankData.first bankHeader : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadFirst, _root_.ThreeSum.SourceBandBankData.first, _root_.ThreeSum.SharedReportingBankHeader.records]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hreadFirst, _root_.ThreeSum.SourceBandBankData.first, _root_.ThreeSum.SharedReportingBankHeader.records] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadFirst, _root_.ThreeSum.SourceBandBankData.first, _root_.ThreeSum.SharedReportingBankHeader.records] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span h J (2 * h * J) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadSpan, haSpan, _root_.ThreeSum.SharedReportingBankHeader.records]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hreadSpan, haSpan, _root_.ThreeSum.SharedReportingBankHeader.records] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadSpan, haSpan, _root_.ThreeSum.SharedReportingBankHeader.records] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hdepthCall := ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.meets
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightSwitchDepth.program_meets (μ := μ) (d := d+1) R.depthWord (by omega))
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingBank.program).append _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingHost.countMap).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingHost.body 67 69 66]
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hdepthCall _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hdepthCall ?_ ?_ ?_ ?_
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
     on_goal -1 => (rintro resultDepth νt ⟨hresultDepth, hmem⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst νt
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SharedReportingBankHeader.levels J : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hresultDepth, _root_.ThreeSum.SharedReportingBankHeader.levels]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hresultDepth, _root_.ThreeSum.SharedReportingBankHeader.levels] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hresultDepth, _root_.ThreeSum.SharedReportingBankHeader.levels] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SharedReportingBankHeader.records free : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.SharedReportingBankHeader.records]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.SharedReportingBankHeader.records] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.SharedReportingBankHeader.records] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hcountCall := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.meets
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCounts.program_meets (μ := μ) (d := d+1) (h := h) (dst := free+7)
      (work := _root_.ThreeSum.SharedReportingBankHeader.records free) hw (by unfold _root_.ThreeSum.SharedReportingBankHeader.records; omega) hconstants hpascal R.powers R.pairs (by omega))
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingHost.depthPrefix).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingHost.body 67 69 66]
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hcountCall _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hcountCall ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.SharedReportingBankHeader.records]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.SharedReportingBankHeader.records] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.SharedReportingBankHeader.records] <;> omega)
     on_goal -1 => (rintro resultPairs ν₁ ⟨hresultPairs, hcounts, hkeepCounts⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hreadH : ν₁ (free+7)=(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localChoose h : ℤ) := by
    simpa [_root_.ThreeSum1960614.Machine.Light.SegN] using hcounts.getD (i := 0) (by simp [_root_.ThreeSum1960614.Machine.Light.SegN]) 0
  have hreadE : ν₁ (free+8)=(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h : ℤ) := by
    simpa [_root_.ThreeSum1960614.Machine.Light.SegN,Nat.add_assoc] using hcounts.getD (i := 1) (by simp [_root_.ThreeSum1960614.Machine.Light.SegN]) 0
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localChoose h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadH, haH, _root_.ThreeSum.SharedReportingBankHeader.records]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hreadH, haH, _root_.ThreeSum.SharedReportingBankHeader.records] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadH, haH, _root_.ThreeSum.SharedReportingBankHeader.records] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.total h J NB NC g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.total, _root_.ThreeSum.SharedReportingBankRows.pairs]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.total, _root_.ThreeSum.SharedReportingBankRows.pairs] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.total, _root_.ThreeSum.SharedReportingBankRows.pairs] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload free h J NB NC g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hkeptFree : _root_.ThreeSum1960614.Machine.Light.Kept μ ν₁ free := fun a ha => hkeepCounts a (by omega)
  have hbankNow := Hbank.of_kept hkeptFree hocc hsource
  have hbankCall := (((_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingBank.program_meets (μ := ν₁) (d := d+1)
    (record := _root_.ThreeSum.SharedReportingBankHeader.records free) (base := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload free h J NB NC g) hbankNow hw (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.levels_pos J)
    (by rfl) hocc (hsource.trans (by unfold _root_.ThreeSum.SharedReportingBankHeader.records; omega)) le_rfl hfinish R.control R.bank).append
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightSwitchDepth.program.map (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingBank.program.length))).append
      _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingHost.countMap).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingHost.body 67 69 66]
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hbankCall _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hbankCall ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hresultPairs]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hresultPairs] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hresultPairs] <;> omega)
     on_goal -1 => (rintro result ν₂ ⟨hresult, hrows, hkeepBank, _⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hresultFinish : result=(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish free h J NB NC g : ℤ) := hresult
  have hreadH₂ : ν₂ (free+7)=(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localChoose h : ℤ) :=
    (hkeepBank _ (by unfold _root_.ThreeSum.SharedReportingBankHeader.records; omega)).trans hreadH
  have hreadE₂ : ν₂ (free+8)=(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h : ℤ) :=
    (hkeepBank _ (by unfold _root_.ThreeSum.SharedReportingBankHeader.records; omega)).trans hreadE
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish free h J NB NC g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hresultFinish]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hresultFinish] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hresultFinish] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen free (_root_.ThreeSum.SharedReportingBankHeader.records free : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.SharedReportingBankHeader.records]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.SharedReportingBankHeader.records] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.SharedReportingBankHeader.records] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (free + 1) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload free h J NB NC g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.SharedReportingBankHeader.records]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.SharedReportingBankHeader.records] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.SharedReportingBankHeader.records] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (free + 2) (_root_.ThreeSum.SharedReportingBankHeader.levels J : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.SharedReportingBankHeader.records]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.SharedReportingBankHeader.records] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.SharedReportingBankHeader.records] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (free + 3) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.SharedReportingBankHeader.records]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.SharedReportingBankHeader.records] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.SharedReportingBankHeader.records] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (free + 4) (_root_.ThreeSum.BandPartition.size NB g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.SharedReportingBankHeader.records]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.SharedReportingBankHeader.records] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.SharedReportingBankHeader.records] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (free + 5) (_root_.ThreeSum.BandPartition.size NC g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.SharedReportingBankHeader.records]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.SharedReportingBankHeader.records] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.SharedReportingBankHeader.records] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (free + 6) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish free h J NB NC g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.SharedReportingBankHeader.records]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.SharedReportingBankHeader.records] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.SharedReportingBankHeader.records] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish free h J NB NC g : ℕ) ?_ ?_ ?_
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
  refine ⟨rfl,⟨?_,?_⟩,?_⟩
  · intro i hi
    have hi' : i < 9 := by simpa [_root_.ThreeSum1960614.Machine.Light.SegN,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.header] using hi
    interval_cases i <;> simp [_root_.ThreeSum1960614.Machine.Light.SegN,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.header,hreadH₂,hreadE₂]
  · apply _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.done_of_after hrows ?_ le_rfl (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.records_le_payload _ _ _ _ _ _)
    intro a ha
    have h0 : a ≠ free := by unfold _root_.ThreeSum.SharedReportingBankHeader.records at ha; omega
    have h1 : a ≠ free+1 := by unfold _root_.ThreeSum.SharedReportingBankHeader.records at ha; omega
    have h2 : a ≠ free+2 := by unfold _root_.ThreeSum.SharedReportingBankHeader.records at ha; omega
    have h3 : a ≠ free+3 := by unfold _root_.ThreeSum.SharedReportingBankHeader.records at ha; omega
    have h4 : a ≠ free+4 := by unfold _root_.ThreeSum.SharedReportingBankHeader.records at ha; omega
    have h5 : a ≠ free+5 := by unfold _root_.ThreeSum.SharedReportingBankHeader.records at ha; omega
    have h6 : a ≠ free+6 := by unfold _root_.ThreeSum.SharedReportingBankHeader.records at ha; omega
    simp [Function.update_of_ne,h0,h1,h2,h3,h4,h5,h6]
  · intro a ha
    have h0 : a ≠ free := by omega
    have h1 : a ≠ free+1 := by omega
    have h2 : a ≠ free+2 := by omega
    have h3 : a ≠ free+3 := by omega
    have h4 : a ≠ free+4 := by omega
    have h5 : a ≠ free+5 := by omega
    have h6 : a ≠ free+6 := by omega
    simp only [Function.update_of_ne h6,Function.update_of_ne h5,Function.update_of_ne h4,
      Function.update_of_ne h3,Function.update_of_ne h2,Function.update_of_ne h1,Function.update_of_ne h0]
    exact (hkeepBank _ (by unfold _root_.ThreeSum.SharedReportingBankHeader.records; omega)).trans (hkeptFree a ha)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightSharedReportingHost.program_meets__implementation_16b9b0f473) := (@ThreeSum1960614.Machine.ThreeSum.LightSharedReportingHost.program_meets__implementation_16b9b0f473)

#print axioms solution
