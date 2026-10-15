-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightEncodedColorReportingPipeline.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:08:43.348053+00:00
-- url     : https://prove2.me/submissions/c0d99495-bebe-483e-90c3-7a05e093116b

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle038
import Definitions.Def_ThreeSum1960614_Machine_Bundle039
import Definitions.Def_ThreeSum1960614_Machine_Bundle040
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
import Definitions.Def_ThreeSum1962Source_Bundle17
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
import Mathlib.Data.Finset.Image
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
import Mathlib.Data.Int.Basic
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
import Mathlib.Data.Nat.Bitwise
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
import Mathlib.Tactic.IntervalCases
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorPipelineData_ordered
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorReportingData_report_le_source_allocation
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorResources_pipeline_space_bound
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightEncodedColorPipeline_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightThreeSumReportingSetup_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_offset_le

local instance platformRadixNonzero_75492a9aaa (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Filter
end Filter
namespace Light
end Light
namespace Real
end Real
namespace ThreeSum
end ThreeSum
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.EncodedColorLayout
end ThreeSum.EncodedColorLayout
namespace ThreeSum.EncodedColorNormalizedData
end ThreeSum.EncodedColorNormalizedData
namespace ThreeSum.EncodedColorPrimeCosts
end ThreeSum.EncodedColorPrimeCosts
namespace ThreeSum.EncodedColorReportingCosts
end ThreeSum.EncodedColorReportingCosts
namespace ThreeSum.EncodedColorReportingResources
end ThreeSum.EncodedColorReportingResources
namespace ThreeSum.EncodedColorResources
end ThreeSum.EncodedColorResources
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter
namespace ThreeSum.LightEncodedColorReportingPipeline
end ThreeSum.LightEncodedColorReportingPipeline
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.ReportingHostRelocation
end ThreeSum.ReportingHostRelocation
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankHeader
end ThreeSum.SharedReportingBankHeader
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SharedReportingBankResourceBounds
end ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum.SharedReportingBankRows
end ThreeSum.SharedReportingBankRows
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.ThreeSumColorBudgets
end ThreeSum.ThreeSumColorBudgets
namespace ThreeSum.ThreeSumReportingSetupData
end ThreeSum.ThreeSumReportingSetupData
namespace ThreeSum.ThreeSumReportingSetupResources
end ThreeSum.ThreeSumReportingSetupResources
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
end ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
namespace ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
end ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
namespace ThreeSum1960614.Machine.ThreeSum.BandEnumeration
end ThreeSum1960614.Machine.ThreeSum.BandEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.BandRawA
end ThreeSum1960614.Machine.ThreeSum.BandRawA
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.ColorClassLists
end ThreeSum1960614.Machine.ThreeSum.ColorClassLists
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
end ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeCosts
end ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeCosts
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingCosts
end ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingCosts
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources
end ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorResources
end ThreeSum1960614.Machine.ThreeSum.EncodedColorResources
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
end ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
namespace ThreeSum1960614.Machine.ThreeSum.LightClassFilter
end ThreeSum1960614.Machine.ThreeSum.LightClassFilter
namespace ThreeSum1960614.Machine.ThreeSum.LightEncodedColorReportingPipeline
end ThreeSum1960614.Machine.ThreeSum.LightEncodedColorReportingPipeline
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
end ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets
end ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
end ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupResources
end ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupResources
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






theorem size_le (n g : ℕ) : _root_.ThreeSum.BandPartition.size n g ≤ n := by
  unfold _root_.ThreeSum.BandPartition.size
  split_ifs with h
  · omega
  · have hdiv := Nat.div_le_self (n-1) g
    omega

theorem size_mono {n m g : ℕ} (h : n ≤ m) : _root_.ThreeSum.BandPartition.size n g ≤ _root_.ThreeSum.BandPartition.size m g := by
  by_cases hn : n = 0
  · simp [_root_.ThreeSum.BandPartition.size,hn]
  · have hm : m ≠ 0 := by omega
    have hd := Nat.div_le_div_right (c := g) (show n-1 ≤ m-1 by omega)
    simp only [_root_.ThreeSum.BandPartition.size,if_neg hn,if_neg hm]
    omega























end ThreeSum.BandPartition

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

/-- More time and a weaker conclusion. -/
theorem Meets.mono (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (hT : T ≤ T') (hR : ∀ r μ', R r μ' → R' r μ') :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T' R' := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, hp, he.mono hT fun _ => hR _ _⟩

/-- A specification holds with every larger bound on the time. -/
theorem Meets.mono_time (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (hT : T ≤ T' := by omega) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T' R :=
  h.mono hT fun _ _ hR => hR



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



























theorem rect_length (m n : ℕ) (F : ℕ → ℕ → _root_.ThreeSum.BandCandidateRows.Record) : (_root_.ThreeSum.BandCandidateRows.rect m n F).length=m*n := by
  simp [_root_.ThreeSum.BandCandidateRows.rect,List.length_flatMap]

theorem records_length (A B C : _root_.ThreeSum.BandEnumeration.Family) :
    (_root_.ThreeSum.BandCandidateRows.records A B C).length=_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size := by
  simp only [_root_.ThreeSum.BandCandidateRows.records,List.length_append,_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.rect_length,_root_.ThreeSum.LightBandEnumeration.count]
  omega

























end ThreeSum.BandCandidateRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Stable extraction of one color class from the original signed array

The program reads stored colors and original values. It writes a length
header followed by exactly the selected values, optionally negated. Repeated
values are preserved; deduplication belongs to the later normalization pass.
-/

namespace ThreeSum.LightClassFilter
open _root_.ThreeSum.LightClassFilter


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1200000







theorem items_length_le (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) :
    (_root_.ThreeSum.LightClassFilter.items x color want scale n).length ≤ n := by
  simpa only [_root_.ThreeSum.LightClassFilter.items,List.length_map,List.length_range] using
    List.length_filter_le (p := fun i => decide (color i = want)) (l := List.range n)











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







end ThreeSum.LightClassFilter

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





/-- A smaller need is allowed for if a larger one is, also with a larger free pointer and at a
larger depth if the sums are not larger. -/
theorem Need.Ok.mono {r r' : _root_.ThreeSum1960614.Machine.Light.Need} {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {fr fr' d d' : ℕ} (h : r.Ok lim fr d)
    (hw : r'.word ≤ r.word) (hc : fr' + r'.cells ≤ fr + r.cells)
    (hd : d' + r'.depth ≤ d + r.depth) : r'.Ok lim fr' d' :=
  ⟨le_trans (by exact_mod_cast hw) h.word, hc.trans h.cells, h.space, hd.trans h.depth⟩



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

/-!
# Exact original-position semantics of the constructed color-class lists

The machine keeps repeated values within a class and negates the third
class. The list membership witnesses are original positions. Any binary
width large enough for the indices suffices for the deterministic family.
-/

namespace ThreeSum.ColorClassLists
open _root_.ThreeSum.ColorClassLists


open _root_.ThreeSum.LightClassFilter
open _root_.ThreeSum1960614.Machine.ThreeSum.LightClassFilter













theorem length_classList_le {n W : ℕ} (p : _root_.ThreeSum.Coloring.Parameter W) (x : Fin n → ℤ)
    (c : ℕ) (scale : ℤ) : (_root_.ThreeSum.ColorClassLists.classList p x c scale).length ≤ n :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightClassFilter.items_length_le ..













end ThreeSum.ColorClassLists

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Explicit finite resource envelopes for the executed shared reporting bank

The envelopes below include the entire header and metadata slab, every
compact payload and construction scratch region, all prefix/local counts,
packed keys, switch intermediates, and both independent source lengths.
They are derived from the actual finite host contract.
-/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum.SharedReportingBankLevels
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels
open _root_.ThreeSum.SharedReportingBankHeader
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader
open _root_.ThreeSum.SharedReportingBankRows
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows

set_option maxHeartbeats 2800000
set_option maxRecDepth 14000
























theorem total_le {NB NC n h J g : ℕ} (hB : NB ≤ n) (hC : NC ≤ n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.total h J NB NC g ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J*n*n :=
  Nat.mul_le_mul (Nat.mul_le_mul_left _ ((_root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le NB g).trans hB))
    ((_root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le NC g).trans hC)

theorem space_le {free h J NB NC g n : ℕ} (hB : NB ≤ n) (hC : NC ≤ n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingHost.space free h J NB NC g ≤ free+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.extent h J n := by
  have hP := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.total_le (h := h) (J := J) (g := g) hB hC
  have ho := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.offset_le h J
  have hm := Nat.mul_le_mul_left (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.total h J NB NC g) ho
  have hp := Nat.mul_le_mul_right (5*_root_.ThreeSum.SharedReportingBankHeader.levels J+_root_.ThreeSum.SharedReportingBankHeader.levels J*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.cellBound h J) hP
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingHost.space
  apply max_le
  · unfold _root_.ThreeSum.SharedReportingBankHeader.records _root_.ThreeSum.LightPascal.tableSize _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.extent
    omega
  · unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.rowBase _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload _root_.ThreeSum.SharedReportingBankHeader.records _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.extent
    nlinarith





end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual finite budgets of the retained common-prime stage -/

namespace ThreeSum.EncodedColorPrimeCosts
open _root_.ThreeSum.EncodedColorPrimeCosts


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds







theorem count_mono {nA nB nC nA' nB' nC' g : ℕ} (ha : nA ≤ nA') (hb : nB ≤ nB') (hc : nC ≤ nC') :
    _root_.ThreeSum.LightEncodedColorPrime.count nA nB nC g ≤ _root_.ThreeSum.LightEncodedColorPrime.count nA' nB' nC' g := by
  have a := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mono (g := g) ha
  have b := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mono (g := g) hb
  have c := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mono (g := g) hc
  unfold _root_.ThreeSum.LightEncodedColorPrime.count
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul b c) (Nat.mul_le_mul a b)) (Nat.mul_le_mul a c)















end ThreeSum.EncodedColorPrimeCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Retained normalized pointers and the actual incidence-count cell -/

namespace ThreeSum.EncodedColorNormalizedData
open _root_.ThreeSum.EncodedColorNormalizedData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum.EncodedColorLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout





theorem records_length_le {A B C : List ℤ} {g n : ℕ} {hg : 0 < g}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (ha : A.length ≤ n) (hb : B.length ≤ n) (hc : C.length ≤ n) :
    (_root_.ThreeSum.BandRawA.sortedRecords A B C g hg hsA hsB hsC).length ≤ _root_.ThreeSum.ColorBandBounds.count n g := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeCosts.count_mono (g := g) ha hb hc
  have hright : _root_.ThreeSum.LightEncodedColorPrime.count n n n g=_root_.ThreeSum.ColorBandBounds.count n g := by
    unfold _root_.ThreeSum.LightEncodedColorPrime.count _root_.ThreeSum.ColorBandBounds.count
    ring
  rw [hright] at h
  simp only [_root_.ThreeSum.BandRawA.sortedRecords, _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.records_length]
  exact h







end ThreeSum.EncodedColorNormalizedData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Polynomial Need for the exact closed selected-color pipeline -/

namespace ThreeSum.EncodedColorResources
open _root_.ThreeSum.EncodedColorResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000













noncomputable section





end

theorem bounds_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {free n U d : ℕ} (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.need n U).Ok lim free d) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.space free n U ≤ lim.space ∧
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.word n U : ℤ) ≤ lim.word ∧
    d+_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.depth n ≤ lim.depth := by
  refine ⟨?_,hok.word,hok.depth⟩
  apply (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.pipeline_space_bound free n U).trans
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.need,Nat.add_assoc] using hok.cells

theorem program_meets {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ → ℤ} {src n params row free U d : ℕ}
    (color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)) (x : Fin n → ℤ)
    (hn : 0 < n) (hR : 4 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n)
    (hsrc : src+n ≤ free) (hparams : params+19 ≤ free) (hrow : row+6 ≤ free)
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.need n U).Ok lim free d)
    (hread : _root_.ThreeSum1960614.Machine.Light.Seg μ src (List.ofFn x)) (hbound : ∀ i, |x i| ≤ (U : ℤ))
    (hparameters : _root_.ThreeSum1960614.Machine.Light.Seg μ params (_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values n))
    (hcolor : _root_.ThreeSum1960614.Machine.Light.Seg μ row (_root_.ThreeSum.ColorParameters.fields color)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.program 255 d [src,n,params,row,free] μ
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.time n U)
      (fun r ν => _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Output ν free n color x r ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν free) := by
  obtain ⟨hs,hw,hd⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.bounds_of_ok hok
  exact _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.program_meets color x hok.space hn hR hsrc hparams hrow
    hs hw hd hread hbound hparameters hcolor

end ThreeSum.EncodedColorResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact finite resources for constructing the dense-stop counter

The power-loop bound includes its actual `(base+1)^(J+1)` intermediate.
The modular scoring workspace remains affine in an arbitrary destination.
-/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.KaratsubaInterface
open _root_.ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface

set_option maxHeartbeats 2300000
set_option maxRecDepth 14000




















theorem dense_space_eq (dst n U : ℕ) :
    _root_.ThreeSum.LightWeightedScore.space (dst+4) (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) U=dst+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.denseCells n U := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.denseCells _root_.ThreeSum.LightWeightedScore.space _root_.ThreeSum.LightModuloCounts.space
  simp only [zero_add]
  omega





end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual encoding-output masses fit the uniform reporting budgets

Both inequalities come from the retained pipeline payload. The wanted
count includes all physical A occurrences and all three lifts; the false
score uses the very common modulus selected from the original normalized
arrays. No input-dependent counting or prime-quality premise is assumed.
The explicit numerical divisor premise is discharged eventually, uniformly
before the input arrays are quantified.
-/

namespace ThreeSum.ThreeSumColorBudgets
open _root_.ThreeSum.ThreeSumColorBudgets


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000





variable {μ : ℕ → ℤ} {free n : ℕ}
    {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n → ℤ}
    {A B C : List ℤ} {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}

theorem normalized_lengths (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    A.length ≤ n ∧ B.length ≤ n ∧ C.length ≤ n :=
  ⟨H.normalized.2.1.2.1.trans (_root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists.length_classList_le color x 0 1),
    H.normalized.2.2.1.2.1.trans (_root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists.length_classList_le color x 1 1),
    H.normalized.2.2.2.1.2.1.trans (_root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists.length_classList_le color x 2 (-1))⟩

















open _root_.Filter



end ThreeSum.ThreeSumColorBudgets

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Polynomial limits for the exact dense initialization resources -/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds

set_option maxHeartbeats 1600000
set_option maxRecDepth 14000













noncomputable section





end

theorem dense_resources_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {dst n U d : ℕ}
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.denseNeed n U).Ok lim dst d) :
    _root_.ThreeSum.LightWeightedScore.space (dst+4) (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) U ≤ lim.space ∧
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.denseWord n U : ℤ) ≤ lim.word ∧ d+Nat.clog 2 (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n)+8 ≤ lim.depth := by
  refine ⟨?_,hok.word,?_⟩
  · rw [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.dense_space_eq]
    exact hok.cells
  · simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.denseNeed,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.denseDepth,Nat.add_assoc] using hok.depth



end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact retained addresses for reporting one encoded original color -/

namespace ThreeSum.ThreeSumReportingSetupData
open _root_.ThreeSum.ThreeSumReportingSetupData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData















theorem prefix_le_report (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    free+8 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC := by
  obtain ⟨_,hf,hc,_,hs,_⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.ordered free n A B C hsA hsB hsC
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase
  omega





end ThreeSum.ThreeSumReportingSetupData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual time of the source, shared reporting and dense prefixProgram -/

namespace ThreeSum.EncodedColorReportingCosts
open _root_.ThreeSum.EncodedColorReportingCosts


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open scoped _root_.Topology

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000







theorem setup_time_le {n U R : ℕ} (hR : R ≤ _root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupBank.time n+_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.time n U R+200 ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingCosts.setupTime n U := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingCosts.setupTime _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.time _root_.ThreeSum.LightDenseSetup.time _root_.ThreeSum.LightBandWeightedScore.time
  gcongr



noncomputable section













end
end ThreeSum.EncodedColorReportingCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual header-loaded dense initialization under its proved Need -/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales

set_option maxHeartbeats 1600000
set_option maxRecDepth 16000

theorem dense_word_eq (n U : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.denseWord n U=_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.word n U := rfl

theorem dense_actual_resources_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {dst n U d : ℕ}
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.denseNeed n U).Ok lim dst d) :
    _root_.ThreeSum.LightWeightedScore.space (dst+4) (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) U ≤ lim.space ∧
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.word n U : ℤ) ≤ lim.word ∧
      d+Nat.clog 2 (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n)+8 ≤ lim.depth := by
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.dense_word_eq] using _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.dense_resources_of_ok hok



end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Compose the two actual reporting allocations at an arbitrary free pointer -/

namespace ThreeSum.ThreeSumReportingSetupResources
open _root_.ThreeSum.ThreeSumReportingSetupResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000



theorem counter_le {μ : ℕ → ℤ} {free n : ℕ}
    {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) (U : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC+
      (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.need n U).cells := by
  obtain ⟨_,hB,hC⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.normalized_lengths H
  exact (le_max_right _ _).trans (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.space_le
    (free := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC) (h := _root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n))
    (J := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (g := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) hB hC)

theorem bank_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {n U report d : ℕ}
    (H : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupResources.need n U).Ok lim report d) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.need n U).Ok lim report (d+2) :=
  H.mono (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupResources.need]; omega) (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupResources.need]; omega) (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupResources.need]; omega)

theorem dense_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {n U report dst d : ℕ}
    (H : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupResources.need n U).Ok lim report d)
    (hdst : dst ≤ report+(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.need n U).cells) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.denseNeed n U).Ok lim dst (d+1) :=
  H.mono (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupResources.need]; omega) (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupResources.need]; omega) (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupResources.need]; omega)

noncomputable section



end
end ThreeSum.ThreeSumReportingSetupResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Affine resources for source construction followed by reporting setup -/

namespace ThreeSum.EncodedColorReportingResources
open _root_.ThreeSum.EncodedColorReportingResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000



theorem source_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {free n U d : ℕ}
    (H : (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources.need n U).Ok lim free d) : (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.need n U).Ok lim free (d+1) :=
  H.mono (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources.need]; omega) (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources.need]; omega) (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources.need]; omega)

theorem setup_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {free report n U d : ℕ}
    (H : (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources.need n U).Ok lim free d)
    (hreport : report ≤ free+(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.need n U).cells) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupResources.need n U).Ok lim report (d+1) :=
  H.mono (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources.need]; omega) (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources.need]; omega) (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources.need]; omega)



noncomputable section



end
end ThreeSum.EncodedColorReportingResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # The concrete reporting preparation under one polynomial resource contract -/

namespace ThreeSum.ThreeSumReportingSetupResources
open _root_.ThreeSum.ThreeSumReportingSetupResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData

set_option maxHeartbeats 1000000

theorem program_meets {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ} {μ : ℕ → ℤ} {free n params U : ℕ}
    {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (Hparams : _root_.ThreeSum1960614.Machine.Light.Seg μ params (_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values n)) (hparams : params+19 ≤ free)
    (hR : 4 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (hx : ∀ i, |x i| ≤ (U : ℤ))
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupResources.need n U).Ok lim (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC) d) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetup.program 97 d
      [n,params,free,_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC] μ
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetup.time n U
        (_root_.ThreeSum.BandRawA.sortedRecords A B C (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n) hsA hsB hsC).length)
      (fun r ν => r=(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.Stored ν free n color x A B C hsA hsB hsC ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC)) := by
  have hbank := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupResources.bank_of_ok hok
  have hdense := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupResources.dense_of_ok hok (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupResources.counter_le H U)
  obtain ⟨hs,hw,hd⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.dense_actual_resources_of_ok hdense
  exact _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetup.program_meets H Hparams hparams hR hbank hs hw
    (by omega) hx

end ThreeSum.ThreeSumReportingSetupResources

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorReportingPipeline

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
set_option maxHeartbeats 2600000
set_option maxRecDepth 17000
section

theorem ThreeSum1960614.Machine.ThreeSum.LightEncodedColorReportingPipeline.program_meets__implementation_f2bdf111a9 {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ → ℤ} {src n params row free U d : ℕ}
    (color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)) (x : Fin n → ℤ)
    (hn : 0 < n) (hR : 4 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n)
    (hsrc : src+n ≤ free) (hparams : params+19 ≤ free) (hrow : row+6 ≤ free)
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources.need n U).Ok lim free d)
    (hread : _root_.ThreeSum1960614.Machine.Light.Seg μ src (List.ofFn x)) (hbound : ∀ i, |x i| ≤ (U : ℤ))
    (hparameters : _root_.ThreeSum1960614.Machine.Light.Seg μ params (_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values n))
    (hcolor : _root_.ThreeSum1960614.Machine.Light.Seg μ row (_root_.ThreeSum.ColorParameters.fields color)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorReportingPipeline.program 354 d [src,n,params,row,free] μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorReportingPipeline.time n U)
      (fun r ν => _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingData.Output ν free n color x r ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν free) := by
  have sourceNeed := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources.source_of_ok hok
  have hw := hok.space
  have hd : d < lim.depth := by have hh := sourceNeed.depth; omega
  have hfreeSpace : free ≤ lim.space := by have hh := hok.cells; omega
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 354) (by rfl : program[354]?=some (body 255 353))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorReportingPipeline.body _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorReportingPipeline.time _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingCosts.time
  have hSource := ((_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.program_meets (d := d+1) (μ := μ)
    color x hn hR hsrc hparams hrow sourceNeed hread hbound hparameters hcolor).append
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetup.program.map (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate 256))).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorReportingPipeline.body 255 353]
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hSource _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hSource ?_ ?_ ?_ ?_
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
     on_goal -1 => (rintro out μ₁ ⟨source₁, keepSource⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  obtain ⟨A,hsA,B,hsB,C,hsC,hout,encoded₁⟩ := source₁
  let header := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC
  let report := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC
  let rs := _root_.ThreeSum.BandRawA.sortedRecords A B C (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n) hsA hsB hsC
  have hout' : out=(header : ℤ) := hout
  have hreport := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingData.report_le_source_allocation encoded₁ hn U
  change report ≤ free+(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.need n U).cells at hreport
  have hreportSpace : report ≤ lim.space := hreport.trans sourceNeed.cells
  have hheader : header+8=report := rfl
  have hheaderWord : (header : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show header ≤ lim.space by omega)).trans hw
  have hprefix := (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.prefix_le_report free n A B C hsA hsB hsC).1
  change free+8 ≤ report at hprefix
  have setupNeed := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources.setup_of_ok hok hreport
  have params₁ : _root_.ThreeSum1960614.Machine.Light.Seg μ₁ params (_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values n) := hparameters.of_kept keepSource (by
    simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,
      _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.values] using hparams)
  obtain ⟨ha,hb,hc⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.normalized_lengths encoded₁
  have hcount : rs.length ≤ _root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) :=
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.records_length_le ha hb hc
  have hSetup := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.meets
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupResources.program_meets (d := d+1) (μ := μ₁)
      encoded₁ params₁ hparams hR hbound setupNeed) _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.program).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorReportingPipeline.body 255 353]
  have hSetupTime : _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetup.time n U rs.length ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingCosts.setupTime n U :=
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingCosts.setup_time_le hcount
  have hSetupBound := hSetup.mono_time hSetupTime
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hSetupBound _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hSetupBound ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hout', rs]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hout', rs] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hout', rs] <;> omega)
     on_goal -1 => (rintro ctr ν ⟨hctr, stored, keepSetup⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (header : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hout']
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hout'] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hout'] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  exact ⟨⟨A,hsA,B,hsB,C,hsC,rfl,stored⟩,
    fun i hi => (keepSetup i (by change i < report; omega)).trans (keepSource i hi)⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightEncodedColorReportingPipeline.program_meets__implementation_f2bdf111a9) := (@ThreeSum1960614.Machine.ThreeSum.LightEncodedColorReportingPipeline.program_meets__implementation_f2bdf111a9)

#print axioms solution
