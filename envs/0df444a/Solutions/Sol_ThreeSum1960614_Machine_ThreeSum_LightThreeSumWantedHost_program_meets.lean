-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:56:22.476284+00:00
-- url     : https://prove2.me/submissions/a6920ff5-c473-4652-89fc-29302b1cff95

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
import Definitions.Def_ThreeSum1962Source_Bundle18
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorParameterData_reads
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorPipelineData_ordered

local instance platformRadixNonzero_7103b1e6ff (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Filter
end Filter
namespace Light
end Light
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
namespace ThreeSum.EncodedColorPipelineData
end ThreeSum.EncodedColorPipelineData
namespace ThreeSum.EncodedColorPrimeCosts
end ThreeSum.EncodedColorPrimeCosts
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter
namespace ThreeSum.LightCoverKeyData
end ThreeSum.LightCoverKeyData
namespace ThreeSum.LightLocalCoverRetention
end ThreeSum.LightLocalCoverRetention
namespace ThreeSum.LightThreeSumWantedHost
end ThreeSum.LightThreeSumWantedHost
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankHeader
end ThreeSum.SharedReportingBankHeader
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SharedReportingBankRows
end ThreeSum.SharedReportingBankRows
namespace ThreeSum.SourceFiniteInputs
end ThreeSum.SourceFiniteInputs
namespace ThreeSum.ThreeSumColorBudgets
end ThreeSum.ThreeSumColorBudgets
namespace ThreeSum.ThreeSumReportingSetupData
end ThreeSum.ThreeSumReportingSetupData
namespace ThreeSum.ThreeSumWantedHostData
end ThreeSum.ThreeSumWantedHostData
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
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeCosts
end ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeCosts
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
end ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightClassFilter
end ThreeSum1960614.Machine.ThreeSum.LightClassFilter
namespace ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData
end ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRetention
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRetention
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
namespace ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost
end ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
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
namespace ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs
end ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets
end ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
end ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData
end ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData
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











theorem length_le (n g i : ℕ) : _root_.ThreeSum.BandPartition.stop n g i-_root_.ThreeSum.BandPartition.start g i ≤ g := by
  have hle : _root_.ThreeSum.BandPartition.stop n g i ≤ (i+1)*g := min_le_right _ _
  unfold _root_.ThreeSum.BandPartition.start
  simp only [Nat.add_mul,Nat.one_mul] at hle
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





































/-- Reading a cell of a segment of natural numbers. -/
theorem SegN.read {l : List ℕ} (h : _root_.ThreeSum1960614.Machine.Light.SegN μ a l) {i : ℕ} (hi : i < l.length) :
    μ (a + i) = ((l.getD i 0 : ℕ) : ℤ) := by
  rw [h i (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]



























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

/-! # Retained local-cover tables survive reuse of the returned free region -/

namespace ThreeSum.LightLocalCoverRetention
open _root_.ThreeSum.LightLocalCoverRetention


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata

set_option maxHeartbeats 1000000

theorem base_le_nextFree (base h : ℕ) : base ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree base h := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw1 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw0 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.maps _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.bitPtr
    _root_.ThreeSum.LightCoverGreedy.total
  omega













end ThreeSum.LightLocalCoverRetention

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



theorem count_succ (n g : ℕ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) (i : ℕ) :
    _root_.ThreeSum.BandRawA.count n g rs (i+1)=_root_.ThreeSum.BandRawA.count n g rs i+(_root_.ThreeSum.BandRawA.row n g i (rs.getD i default)).length := by
  simp only [_root_.ThreeSum.BandRawA.count,_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.firstRows_succ,List.length_append]



theorem count_bound (n g : ℕ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) (i : ℕ) : _root_.ThreeSum.BandRawA.count n g rs i ≤ g*i := by
  induction i with
  | zero => simp [_root_.ThreeSum.BandRawA.count,_root_.ThreeSum.BandRawA.firstRows]
  | succ i ih =>
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.count_succ]
    have hh := _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.row_length_le n g i (rs.getD i default)
    nlinarith

theorem items_length_le (n g : ℕ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) : (_root_.ThreeSum.BandRawA.items n g rs).length ≤ g*rs.length :=
  _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.count_bound n g rs rs.length























end ThreeSum.BandRawA

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
# The retained cover, output layers, and exact global key array

This bundle is produced by the actual cover/key host and remains valid when
later phases use its computed next free address. In particular the output
index decoder can read the original layer masks without reconstructing them.
-/

namespace ThreeSum.LightCoverKeyData
open _root_.ThreeSum.LightCoverKeyData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000





theorem layer_end_le_header (free h J : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.afterCover free h+_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.keyHeader free h J := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.keyHeader _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.scratch
  omega

theorem afterCover_le_keyEnd (free h J : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.afterCover free h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd free h J := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.layer_end_le_header free h J
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd
  omega











end ThreeSum.LightCoverKeyData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # One compact retained layout for a selected color -/

namespace ThreeSum.EncodedColorLayout
open _root_.ThreeSum.EncodedColorLayout





















theorem normalized_ends_before_count (free n g : ℕ) :
    _root_.ThreeSum.EncodedColorLayout.av free n+n ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ∧ _root_.ThreeSum.EncodedColorLayout.ae free n+2+2*n ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ∧
    _root_.ThreeSum.EncodedColorLayout.bv free n+n ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ∧ _root_.ThreeSum.EncodedColorLayout.be free n+2+2*n ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ∧
    _root_.ThreeSum.EncodedColorLayout.cv free n+n ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ∧ _root_.ThreeSum.EncodedColorLayout.ce free n+2+2*n ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ∧
    _root_.ThreeSum.EncodedColorLayout.tables free n+_root_.ThreeSum.ColorBandBounds.count n g ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ∧
    _root_.ThreeSum.EncodedColorLayout.rec free n g+4*_root_.ThreeSum.ColorBandBounds.count n g ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g := by
  unfold _root_.ThreeSum.EncodedColorLayout.normalizedEnd _root_.ThreeSum.LightBandRawA.space _root_.ThreeSum.LightBandRawA.positionBase _root_.ThreeSum.LightBandRawA.ownerBase
    _root_.ThreeSum.LightBandRawA.capacity _root_.ThreeSum.EncodedColorLayout.vals _root_.ThreeSum.EncodedColorLayout.rec _root_.ThreeSum.EncodedColorLayout.tables _root_.ThreeSum.EncodedColorLayout.ce _root_.ThreeSum.EncodedColorLayout.cv _root_.ThreeSum.EncodedColorLayout.be _root_.ThreeSum.EncodedColorLayout.bv _root_.ThreeSum.EncodedColorLayout.ae _root_.ThreeSum.EncodedColorLayout.av
  omega







theorem prime_le_cover (free n g M y : ℕ) : _root_.ThreeSum.EncodedColorLayout.prime free n g+6 ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y := by
  unfold _root_.ThreeSum.EncodedColorLayout.cover _root_.ThreeSum.EncodedColorPrimeData.nextFree _root_.ThreeSum.EncodedColorPrimeData.prefixBase _root_.ThreeSum.EncodedColorPrimeData.poolBase
  omega

theorem normalized_ends_cover (free n g M y : ℕ) :
    _root_.ThreeSum.EncodedColorLayout.av free n+n ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧ _root_.ThreeSum.EncodedColorLayout.ae free n+2+2*n ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧
    _root_.ThreeSum.EncodedColorLayout.bv free n+n ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧ _root_.ThreeSum.EncodedColorLayout.be free n+2+2*n ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧
    _root_.ThreeSum.EncodedColorLayout.cv free n+n ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧ _root_.ThreeSum.EncodedColorLayout.ce free n+2+2*n ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧
    _root_.ThreeSum.EncodedColorLayout.tables free n+_root_.ThreeSum.ColorBandBounds.count n g ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧
    _root_.ThreeSum.EncodedColorLayout.rec free n g+4*_root_.ThreeSum.ColorBandBounds.count n g ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧
    _root_.ThreeSum.LightBandRawA.space (_root_.ThreeSum.EncodedColorLayout.vals free n g) (_root_.ThreeSum.ColorBandBounds.count n g) g ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout.normalized_ends_before_count free n g
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout.prime_le_cover free n g M y
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ≤ _
  unfold _root_.ThreeSum.EncodedColorLayout.prime at h
  omega

end ThreeSum.EncodedColorLayout

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








theorem records_le_payload (free h J NB NC g : ℕ) :
    _root_.ThreeSum.SharedReportingBankHeader.records free ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload free h J NB NC g := Nat.le_add_right _ _
theorem payload_le_finish (free h J NB NC g : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload free h J NB NC g ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish free h J NB NC g := Nat.le_add_right _ _














end ThreeSum.SharedReportingBankHeader

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Concrete source inputs from the retained normalization and wanted outputs -/

namespace ThreeSum.SourceFiniteInputs
open _root_.ThreeSum.SourceFiniteInputs


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule












theorem prepared_headers {μ : ℕ → ℤ} {values endpoints g : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Represents μ values endpoints g hg original L hs) :
    μ endpoints=(L.length : ℤ) ∧ μ (endpoints+1)=(_root_.ThreeSum.BandPartition.size L.length g : ℤ) :=
  ⟨H.2.2.2.1,H.2.2.2.2.1⟩









end ThreeSum.SourceFiniteInputs

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





theorem heads_read {μ : ℕ → ℤ} {free n g : ℕ} (H : _root_.ThreeSum1960614.Machine.Light.Seg μ free (_root_.ThreeSum.EncodedColorLayout.normalizedHeads free n g)) :
    μ free=(_root_.ThreeSum.EncodedColorLayout.av free n : ℤ) ∧ μ (free+1)=(_root_.ThreeSum.EncodedColorLayout.ae free n : ℤ) ∧
    μ (free+2)=(_root_.ThreeSum.EncodedColorLayout.bv free n : ℤ) ∧ μ (free+3)=(_root_.ThreeSum.EncodedColorLayout.be free n : ℤ) ∧
    μ (free+4)=(_root_.ThreeSum.EncodedColorLayout.cv free n : ℤ) ∧ μ (free+5)=(_root_.ThreeSum.EncodedColorLayout.ce free n : ℤ) ∧
    μ (free+6)=(_root_.ThreeSum.EncodedColorLayout.rec free n g : ℤ) ∧ μ (free+7)=(_root_.ThreeSum.EncodedColorLayout.vals free n g : ℤ) := by
  have h (i : ℕ) (hi : i < 8) := H.getD (i := i) (by simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using hi) 0
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using h 0 (by omega)
  · simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using h 1 (by omega)
  · simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using h 2 (by omega)
  · simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using h 3 (by omega)
  · simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using h 4 (by omega)
  · simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using h 5 (by omega)
  · simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using h 6 (by omega)
  · simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using h 7 (by omega)

end ThreeSum.EncodedColorNormalizedData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Keep the complete selected-color payload while later stages extend memory -/

namespace ThreeSum.EncodedColorPipelineData
open _root_.ThreeSum.EncodedColorPipelineData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000

theorem Stored.heads_read {μ : ℕ → ℤ} {free n : ℕ} {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)}
    {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    let out := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC
    μ out=(_root_.ThreeSum.EncodedColorLayout.prime free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) : ℤ) ∧
    μ (out+1)=(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n : ℤ) ∧
    μ (out+2)=(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.wantedHeader free n (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length : ℤ) ∧
    μ (out+3)=(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC : ℤ) ∧
    μ (out+4)=(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.bankHeader free n A B C hsA hsB hsC : ℤ) ∧
    μ (out+5)=(out+8 : ℕ) ∧
    μ (out+6)=((_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length : ℤ) ∧
    μ (out+7)=(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values] using H.heads.getD (i := 0) (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values]) 0
  · simpa [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values] using H.heads.getD (i := 1) (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values]) 0
  · simpa [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values] using H.heads.getD (i := 2) (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values]) 0
  · simpa [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values] using H.heads.getD (i := 3) (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values]) 0
  · simpa [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values] using H.heads.getD (i := 4) (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values]) 0
  · simpa [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values] using H.heads.getD (i := 5) (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values]) 0
  · simpa [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values] using H.heads.getD (i := 6) (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values]) 0
  · simpa [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values] using H.heads.getD (i := 7) (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.values,_root_.ThreeSum.LightEncodedColorResult.values]) 0





end ThreeSum.EncodedColorPipelineData

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

/-! # Exact retained addresses for reporting one encoded original color -/

namespace ThreeSum.ThreeSumReportingSetupData
open _root_.ThreeSum.ThreeSumReportingSetupData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData













theorem report_le_counter (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC+9 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.records_le_payload ..).trans
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload_le_finish ..)

theorem prefix_le_report (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    free+8 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC := by
  obtain ⟨_,hf,hc,_,hs,_⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.ordered free n A B C hsA hsB hsC
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase
  omega

theorem cover_end_le_report (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n)
      (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC := by
  obtain ⟨_,_,_,hw,hs,_⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.ordered free n A B C hsA hsB hsC
  have he : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.wantedHeader free n (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length=
      _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n)
        (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))+3*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length := rfl
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase
  omega



end ThreeSum.ThreeSumReportingSetupData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # The wanted consumer's configuration from the actual retained color payload -/

namespace ThreeSum.ThreeSumWantedHostData
open _root_.ThreeSum.ThreeSumWantedHostData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData









theorem recordCount_eq (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.recordCount n A B C hsA hsB hsC=
      _root_.ThreeSum.BandPartition.size B.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)*_root_.ThreeSum.BandPartition.size C.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)+
      _root_.ThreeSum.BandPartition.size A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)*_root_.ThreeSum.BandPartition.size B.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)+
      _root_.ThreeSum.BandPartition.size A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)*_root_.ThreeSum.BandPartition.size C.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.recordCount,_root_.ThreeSum.BandRawA.sortedRecords,_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.records_length]
  rfl



theorem pairs_read {μ : ℕ→ℤ} {free n : ℕ}
    {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    μ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.wantedHeader free n (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length+1)=
      ((_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).pairs : ℤ) := H.wanted.2.1

end ThreeSum.ThreeSumWantedHostData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Small independent header and numeric facts used by the concrete loader -/

namespace ThreeSum.LightThreeSumWantedHost
open _root_.ThreeSum.LightThreeSumWantedHost


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales

set_option maxHeartbeats 1200000

theorem word_bounds (n : ℕ) :
    n≤_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.word n ∧ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)≤_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.word n ∧ _root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)≤_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.word n ∧
    _root_.ThreeSum.LightSwitchDepth.depth (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))+1≤_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.word n ∧ _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n≤_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.word n ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n≤_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.word n ∧ _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n))≤_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.word n ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n))≤_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.word n ∧
    _root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)≤_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.word n ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n*_root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)≤_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.word n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.word
  omega

theorem cover_header_reads {μ : ℕ→ℤ} {cover h J : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.Stored μ cover h J) :
    μ cover=(_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h : ℤ) ∧
    μ (cover+10)=(_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h : ℤ) ∧
    μ (cover+18)=(_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.afterCover cover h : ℤ) := by
  have Hread (i : ℕ) (hi : i<20) := H.header.getD (i := i)
    (by simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values,
      _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.values] using hi) 0
  refine ⟨?_,?_,?_⟩
  · simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values,
      _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount] using Hread 0 (by omega)
  · simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values,
      _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.values] using Hread 10 (by omega)
  · simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values,
      _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.afterCover] using Hread 18 (by omega)

theorem report_level_read {μ : ℕ→ℤ} {report h J NB NC g : ℕ} {fB fC : ℕ→ℤ} {p shift : ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.Stored μ report h J NB NC g fB fC p shift) :
    μ (report+2)=((_root_.ThreeSum.LightSwitchDepth.depth J+1 : ℕ) : ℤ) := by
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.header,List.getD_cons_zero,List.getD_cons_succ,
    _root_.ThreeSum.SharedReportingBankHeader.levels] using H.heads.read (i := 2)
      (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.header])

end ThreeSum.LightThreeSumWantedHost

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

namespace ThreeSum.LightThreeSumWantedHost
open _root_.ThreeSum.LightThreeSumWantedHost


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData

set_option diagnostics true
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000



section

private theorem private_0b5842579e_natAddToNat (a b : ℕ) : ((a : ℤ)+(b : ℤ)).toNat=a+b := by omega
end


/- The execution lemma deliberately has only numeric controls.  Keeping the
   normalized arrays and source-bank definitions out of this proof avoids
   repeatedly reducing them while checking every individual header read. -/
section

private theorem private_c62404e87e_header_meets {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d T : ℕ} {μ : ℕ→ℤ}
    {n params free out ctr report cover controls bank ae bv be cv ce vals recs : ℕ}
    {h J K g R N wanted cnt pairs layers schedule masks owners M NB NC gA gB gC : ℕ}
    {Q : ℤ→(ℕ→ℤ)→Prop}
    (hparams : params+19≤free) (hw : (lim.space : ℤ)≤lim.word)
    (hd : d<lim.depth) (hspace : ctr+50≤lim.space)
    (hreport : report+9≤ctr) (hout : out+8=report) (hfree : free+8≤report)
    (hcover : cover≤report) (hwanted : wanted+4≤controls)
    (hcontrols : controls+3≤out) (hbank : bank+5≤out)
    (hcover20 : cover+20≤ masks) (hmasks : masks≤report)
    (hpairs : pairs+2*cnt=controls)
    (hae : ae+2≤cover) (hbv : bv+NB≤cover) (hbe : be+2≤cover)
    (hcv : cv+NC≤cover) (hce : ce+2≤cover) (hrec : recs≤cover)
    (howner : owners≤cover) (hval : vals≤cover)
    (hnB : NB≤n) (hnC : NC≤n) (hGA : gA≤n) (hGB : gB≤n) (hGC : gC≤n)
    (hnword : (n : ℤ)≤lim.word) (hJword : (J : ℤ)≤lim.word)
    (hhword : (h : ℤ)≤lim.word) (hKword : ((K+1 : ℕ) : ℤ)≤lim.word)
    (hgword : (g : ℤ)≤lim.word) (hMword : (M : ℤ)≤lim.word)
    (hlword : (layers : ℤ)≤lim.word) (hsword : (schedule : ℤ)≤lim.word)
    (hRword : (R : ℤ)≤lim.word) (hNword : (N : ℤ)≤lim.word)
    (hReq : R=gB*gC+gA*gB+gA*gC)
    (hownerZ : (vals : ℤ)+(g : ℤ)*(R : ℤ)=(owners : ℤ))
    (readCover : μ (out+1)=(cover : ℤ)) (readWanted : μ (out+2)=(wanted : ℤ))
    (readControls : μ (out+3)=(controls : ℤ)) (readBank : μ (out+4)=(bank : ℤ))
    (readN : μ (out+6)=(N : ℤ)) (readAE : μ (free+1)=(ae : ℤ))
    (readB : μ (free+2)=(bv : ℤ)) (readBE : μ (free+3)=(be : ℤ))
    (readC : μ (free+4)=(cv : ℤ)) (readCE : μ (free+5)=(ce : ℤ))
    (readRecs : μ (free+6)=(recs : ℤ)) (readVals : μ (free+7)=(vals : ℤ))
    (readH : μ (params+1)=(h : ℤ)) (readJ : μ (params+3)=(J : ℤ))
    (readM : μ (params+14)=(M : ℤ)) (readG : μ (params+17)=(g : ℤ))
    (readGA : μ (ae+1)=(gA : ℤ)) (readGB : μ (be+1)=(gB : ℤ))
    (readGC : μ (ce+1)=(gC : ℤ)) (readNB : μ be=(NB : ℤ))
    (readNC : μ ce=(NC : ℤ)) (readCount : μ wanted=(cnt : ℤ))
    (readPairs : μ (wanted+1)=(pairs : ℤ))
    (readLevels : μ (report+2)=((K+1 : ℕ) : ℤ))
    (readLayers : μ cover=(layers : ℤ)) (readSchedule : μ (cover+10)=(schedule : ℤ))
    (readMasks : μ (cover+18)=(masks : ℤ))
    (hscan : _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScan.program 152 (d+1)
      [cnt,(ctr+4 : ℕ),J,h,K,N,NB,NC,cover,ctr,pairs,layers,schedule,masks,vals,owners,recs,
        (controls+3 : ℕ),bank,bv,cv,report,M] μ T Q) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.program 153 d [n,params,free,out,ctr] μ (T+4000) Q := by
  have hRsum : (gB : ℤ)*(gC : ℤ)+(gA : ℤ)*(gB : ℤ)+(gA : ℤ)*(gC : ℤ)≤lim.word := by
    simpa only [hReq,Nat.cast_add,Nat.cast_mul] using hRword
  have hBC0 : (0 : ℤ)≤(gB : ℤ)*(gC : ℤ) := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hAB0 : (0 : ℤ)≤(gA : ℤ)*(gB : ℤ) := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hAC0 : (0 : ℤ)≤(gA : ℤ)*(gC : ℤ) := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have out1 : ((out : ℤ)+1).toNat=out+1 := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.private_0b5842579e_natAddToNat out 1
  have out2 : ((out : ℤ)+2).toNat=out+2 := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.private_0b5842579e_natAddToNat out 2
  have out3 : ((out : ℤ)+3).toNat=out+3 := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.private_0b5842579e_natAddToNat out 3
  have out4 : ((out : ℤ)+4).toNat=out+4 := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.private_0b5842579e_natAddToNat out 4
  have out6 : ((out : ℤ)+6).toNat=out+6 := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.private_0b5842579e_natAddToNat out 6
  have free1 : ((free : ℤ)+1).toNat=free+1 := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.private_0b5842579e_natAddToNat free 1
  have free2 : ((free : ℤ)+2).toNat=free+2 := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.private_0b5842579e_natAddToNat free 2
  have free3 : ((free : ℤ)+3).toNat=free+3 := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.private_0b5842579e_natAddToNat free 3
  have free4 : ((free : ℤ)+4).toNat=free+4 := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.private_0b5842579e_natAddToNat free 4
  have free5 : ((free : ℤ)+5).toNat=free+5 := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.private_0b5842579e_natAddToNat free 5
  have free6 : ((free : ℤ)+6).toNat=free+6 := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.private_0b5842579e_natAddToNat free 6
  have free7 : ((free : ℤ)+7).toNat=free+7 := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.private_0b5842579e_natAddToNat free 7
  have par1 : ((params : ℤ)+1).toNat=params+1 := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.private_0b5842579e_natAddToNat params 1
  have par3 : ((params : ℤ)+3).toNat=params+3 := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.private_0b5842579e_natAddToNat params 3
  have par14 : ((params : ℤ)+14).toNat=params+14 := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.private_0b5842579e_natAddToNat params 14
  have par17 : ((params : ℤ)+17).toNat=params+17 := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.private_0b5842579e_natAddToNat params 17
  have report2 : ((report : ℤ)+2).toNat=report+2 := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.private_0b5842579e_natAddToNat report 2
  have wanted1 : ((wanted : ℤ)+1).toNat=wanted+1 := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.private_0b5842579e_natAddToNat wanted 1
  have cover10 : ((cover : ℤ)+10).toNat=cover+10 := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.private_0b5842579e_natAddToNat cover 10
  have cover18 : ((cover : ℤ)+18).toNat=cover+18 := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.private_0b5842579e_natAddToNat cover 18
  have ae1 : ((ae : ℤ)+1).toNat=ae+1 := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.private_0b5842579e_natAddToNat ae 1
  have be1 : ((be : ℤ)+1).toNat=be+1 := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.private_0b5842579e_natAddToNat be 1
  have ce1 : ((ce : ℤ)+1).toNat=ce+1 := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.private_0b5842579e_natAddToNat ce 1
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 153) (by rfl : program[153]?=some (body 152))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.body
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (ctr + 4 : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (J : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readJ, par3]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [readJ, par3] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readJ, par3] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readH, par1]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [readH, par1] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readH, par1] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (report : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hout]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [hout] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hout] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (K + 1 : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readLevels, report2]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [readLevels, report2] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readLevels, report2] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (K : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (N : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readN, out6]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [readN, out6] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readN, out6] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (ae : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readAE, free1]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [readAE, free1] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readAE, free1] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (be : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readBE, free3]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [readBE, free3] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readBE, free3] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (ce : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readCE, free5]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [readCE, free5] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readCE, free5] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (NB : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readNB]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [readNB] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readNB] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (NC : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readNC]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [readNC] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readNC] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (cover : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readCover, out1]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [readCover, out1] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readCover, out1] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (wanted : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readWanted, out2]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [readWanted, out2] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readWanted, out2] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (cnt : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readCount]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [readCount] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readCount] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (pairs : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readPairs, wanted1]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [readPairs, wanted1] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readPairs, wanted1] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (layers : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readLayers]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [readLayers] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readLayers] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (schedule : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readSchedule, cover10]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [readSchedule, cover10] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readSchedule, cover10] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (masks : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readMasks, cover18]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [readMasks, cover18] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readMasks, cover18] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (vals : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readVals, free7]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [readVals, free7] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readVals, free7] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (recs : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readRecs, free6]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [readRecs, free6] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readRecs, free6] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (controls : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readControls, out3]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [readControls, out3] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readControls, out3] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (controls + 3 : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (bank : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readBank, out4]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [readBank, out4] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readBank, out4] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (bv : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readB, free2]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [readB, free2] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readB, free2] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (cv : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readC, free4]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [readC, free4] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readC, free4] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (M : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readM, par14]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [readM, par14] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readM, par14] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readG, par17]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [readG, par17] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readG, par17] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (gA : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readGA, ae1]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [readGA, ae1] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readGA, ae1] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (gB : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readGB, be1]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [readGB, be1] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readGB, be1] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (gC : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readGC, ce1]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [readGC, ce1] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readGC, ce1] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (R : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hReq]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [hReq] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hReq] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (owners : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hownerZ]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [hownerZ] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hownerZ] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hrun := hscan.append [_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.body 152]
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hrun _ (by ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hrun ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
           first
           | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
           | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
       | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
       |
         (simp [] <;>
             first
             | ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
             | (ring_nf; ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)))
     on_goal -1 => ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega))
     on_goal -1 => (rintro result ν hQ; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  exact hQ
end




end ThreeSum.LightThreeSumWantedHost

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
set_option diagnostics true
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000
section

theorem ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.program_meets__implementation_f11fb1a34c {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d T : ℕ} {μ : ℕ→ℤ} {free n params : ℕ}
    {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    {Q : ℤ→(ℕ→ℤ)→Prop}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
    (Hparams : _root_.ThreeSum1960614.Machine.Light.Seg μ params (_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values n)) (hparams : params+19≤free)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d<lim.depth)
    (hspace : _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC+50+2*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)≤lim.space)
    (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.word n : ℤ)≤lim.word)
    (hscan : _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScan.program 152 (d+1)
      (_root_.ThreeSum.LightReportingWantedDispatch.arguments (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC)
        (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC)) μ T Q) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.program 153 d
      [n,params,free,_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC,
        _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC] μ (T+4000) Q := by
  let out := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC
  let ctr := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC
  let report := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC
  let cover := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n
  let controls := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC
  let bank := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.bankHeader free n A B C hsA hsB hsC
  let ae := _root_.ThreeSum.EncodedColorLayout.ae free n
  let bv := _root_.ThreeSum.EncodedColorLayout.bv free n
  let be := _root_.ThreeSum.EncodedColorLayout.be free n
  let cv := _root_.ThreeSum.EncodedColorLayout.cv free n
  let ce := _root_.ThreeSum.EncodedColorLayout.ce free n
  let vals := _root_.ThreeSum.EncodedColorLayout.vals free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
  let recs := _root_.ThreeSum.EncodedColorLayout.rec free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
  let h := _root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)
  let J := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)
  let K := _root_.ThreeSum.LightSwitchDepth.depth J
  let g := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n
  let R := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.recordCount n A B C hsA hsB hsC
  let N := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length
  let wanted := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.wantedHeader free n N
  let cnt := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC
  let pairs := _root_.ThreeSum.LightWantedSetup.pairBase wanted (3*N) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n)
  let layers := _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h
  let schedule := _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h
  let masks := _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.afterCover cover h
  let owners := _root_.ThreeSum.LightBandRawA.ownerBase vals R g
  have hreport := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.report_le_counter free n A B C hsA hsB hsC
  change report+9≤ctr at hreport
  have hout : out+8=report := rfl
  obtain ⟨hfree,hcover⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.prefix_le_report free n A B C hsA hsB hsC
  change free+8≤report at hfree
  change cover≤report at hcover
  obtain ⟨_,_,_,hwanted,hcontrols,hbank⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.ordered free n A B C hsA hsB hsC
  change wanted+4≤controls at hwanted
  change controls+3≤out at hcontrols
  change bank+5≤out at hbank
  have hcover20 : cover+20≤ masks := by
    exact _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRetention.base_le_nextFree (_root_.ThreeSum.LightLocalCoverInit.base cover) h
  have hmasks := (_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.afterCover_le_keyEnd cover h J).trans
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.cover_end_le_report free n A B C hsA hsB hsC)
  change masks≤report at hmasks
  have hpairs : pairs+2*cnt=controls := rfl
  obtain ⟨hnA,hnB,hnC⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.normalized_lengths H.encoded
  have hR := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.records_length_le (g := g) (hg := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n)
    (hsA := hsA) (hsB := hsB) (hsC := hsC) hnA hnB hnC
  change R≤_root_.ThreeSum.ColorBandBounds.count n g at hR
  have hN : N≤g*_root_.ThreeSum.ColorBandBounds.count n g := by
    unfold N _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences
    rw [_root_.ThreeSum.BandRawA.values_length]
    exact (_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.items_length_le ..).trans (Nat.mul_le_mul_left _ hR)
  obtain ⟨_,hae,hbv,hbe,hcv,hce,_,hrec,hvals⟩ :=
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout.normalized_ends_cover free n g (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum.Scales.primeWindow n)
  change ae+2+2*n≤cover at hae
  change bv+n≤cover at hbv
  change be+2+2*n≤cover at hbe
  change cv+n≤cover at hcv
  change ce+2+2*n≤cover at hce
  change recs+4*_root_.ThreeSum.ColorBandBounds.count n g≤cover at hrec
  change _root_.ThreeSum.LightBandRawA.space vals (_root_.ThreeSum.ColorBandBounds.count n g) g≤cover at hvals
  have howner : owners≤cover := by
    have hh := Nat.mul_le_mul_left g hR
    unfold owners _root_.ThreeSum.LightBandRawA.ownerBase _root_.ThreeSum.LightBandRawA.capacity
    unfold _root_.ThreeSum.LightBandRawA.space _root_.ThreeSum.LightBandRawA.positionBase _root_.ThreeSum.LightBandRawA.ownerBase
      _root_.ThreeSum.LightBandRawA.capacity at hvals
    ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
  have hval : vals≤cover := by
    unfold owners _root_.ThreeSum.LightBandRawA.ownerBase _root_.ThreeSum.LightBandRawA.capacity at howner
    ((try clear H); (try clear Hparams); (try clear hscan); (try clear readCover); (try clear readWanted); (try clear readControls); (try clear readBank); (try clear readN); (try clear readAE); (try clear readB); (try clear readBE); (try clear readC); (try clear readCE); (try clear readRecs); (try clear readVals); (try clear readH); (try clear readJ); (try clear readM); (try clear readG); (try clear readGA); (try clear readGB); (try clear readGC); (try clear readNB); (try clear readNC); (try clear readCount); (try clear readPairs); (try clear readLevels); (try clear readLayers); (try clear readSchedule); (try clear readMasks); omega)
  have hbound (z : ℕ) (hz : z≤_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.word n) : (z : ℤ)≤lim.word := (Int.ofNat_le.mpr hz).trans hword
  obtain ⟨wn,wJ,wh,wK,wg,wM,wl,ws,wR,wN⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.word_bounds n
  have hnword := hbound n wn
  have hJword := hbound J wJ
  have hhword := hbound h wh
  have hKword := hbound (K+1) wK
  have hgword := hbound g wg
  have hMword := hbound (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) wM
  have hlword := hbound layers wl
  have hsword := hbound schedule ws
  have hRword := hbound R (hR.trans wR)
  have hNword := hbound N (hN.trans wN)
  have hGA := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le A.length g
  have hGB := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le B.length g
  have hGC := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le C.length g
  have hReq : R=_root_.ThreeSum.BandPartition.size B.length g*_root_.ThreeSum.BandPartition.size C.length g+_root_.ThreeSum.BandPartition.size A.length g*_root_.ThreeSum.BandPartition.size B.length g+
      _root_.ThreeSum.BandPartition.size A.length g*_root_.ThreeSum.BandPartition.size C.length g := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.recordCount_eq ..
  have hownerZ : (vals : ℤ)+(g : ℤ)*(R : ℤ)=(owners : ℤ) := by
    simp only [owners,_root_.ThreeSum.LightBandRawA.ownerBase,_root_.ThreeSum.LightBandRawA.capacity,Nat.cast_add,Nat.cast_mul]
  obtain ⟨_,readCover,readWanted,readControls,readBank,_,readN,_⟩ := H.encoded.heads_read
  change μ (out+1)=(cover : ℤ) at readCover
  change μ (out+2)=(wanted : ℤ) at readWanted
  change μ (out+3)=(controls : ℤ) at readControls
  change μ (out+4)=(bank : ℤ) at readBank
  change μ (out+6)=(N : ℤ) at readN
  obtain ⟨_,readAE,readB,readBE,readC,readCE,readRecs,readVals⟩ :=
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.heads_read H.encoded.normalizedHeads
  change μ (free+1)=(ae : ℤ) at readAE
  change μ (free+2)=(bv : ℤ) at readB
  change μ (free+3)=(be : ℤ) at readBE
  change μ (free+4)=(cv : ℤ) at readC
  change μ (free+5)=(ce : ℤ) at readCE
  change μ (free+6)=(recs : ℤ) at readRecs
  change μ (free+7)=(vals : ℤ) at readVals
  obtain ⟨_,readH,readJ,_,readM,readG,_⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorParameterData.reads Hparams
  change μ (params+1)=(h : ℤ) at readH
  change μ (params+3)=(J : ℤ) at readJ
  change μ (params+17)=(g : ℤ) at readG
  obtain ⟨_,readGA⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.prepared_headers H.encoded.normalized.2.1
  obtain ⟨readNB,readGB⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.prepared_headers H.encoded.normalized.2.2.1
  obtain ⟨readNC,readGC⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.prepared_headers H.encoded.normalized.2.2.2.1
  change μ (ae+1)=(_root_.ThreeSum.BandPartition.size A.length g : ℤ) at readGA
  change μ (be+1)=(_root_.ThreeSum.BandPartition.size B.length g : ℤ) at readGB
  change μ (ce+1)=(_root_.ThreeSum.BandPartition.size C.length g : ℤ) at readGC
  change μ be=(B.length : ℤ) at readNB
  change μ ce=(C.length : ℤ) at readNC
  have readCount : μ wanted=(cnt : ℤ) := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count_read H.encoded
  have readPairs : μ (wanted+1)=(pairs : ℤ) := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.pairs_read H.encoded
  have readLevels : μ (report+2)=((K+1 : ℕ) : ℤ) := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.report_level_read H.catalog
  obtain ⟨readLayers,readSchedule,readMasks⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.cover_header_reads H.encoded.cover
  change μ cover=(layers : ℤ) at readLayers
  change μ (cover+10)=(schedule : ℤ) at readSchedule
  change μ (cover+18)=(masks : ℤ) at readMasks
  change _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScan.program 152 (d+1)
    [cnt,(ctr+4 : ℕ),J,h,K,N,B.length,C.length,cover,ctr,pairs,layers,schedule,masks,
      vals,owners,recs,(controls+3 : ℕ),bank,bv,cv,report,_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n] μ T Q at hscan
  exact _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.private_c62404e87e_header_meets hparams hw hd
    ((Nat.le_add_right (ctr+50) (2*J)).trans hspace)
    hreport hout hfree hcover hwanted hcontrols hbank hcover20 hmasks hpairs
    ((Nat.le_add_right (ae+2) (2*n)).trans hae)
    ((Nat.add_le_add_left hnB bv).trans hbv)
    ((Nat.le_add_right (be+2) (2*n)).trans hbe)
    ((Nat.add_le_add_left hnC cv).trans hcv)
    ((Nat.le_add_right (ce+2) (2*n)).trans hce)
    ((Nat.le_add_right recs (4*_root_.ThreeSum.ColorBandBounds.count n g)).trans hrec)
    howner hval hnB hnC (hGA.trans hnA) (hGB.trans hnB) (hGC.trans hnC)
    hnword hJword hhword hKword hgword hMword hlword hsword hRword hNword hReq hownerZ
    readCover readWanted readControls readBank readN readAE readB readBE readC readCE
    readRecs readVals readH readJ readM readG readGA readGB readGC readNB readNC
    readCount readPairs readLevels readLayers readSchedule readMasks hscan
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.program_meets__implementation_f11fb1a34c) := (@ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.program_meets__implementation_f11fb1a34c)

#print axioms solution
