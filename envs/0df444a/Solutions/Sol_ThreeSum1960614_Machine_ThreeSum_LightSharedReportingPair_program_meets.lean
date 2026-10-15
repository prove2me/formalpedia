-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightSharedReportingPair.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:47:15.398705+00:00
-- url     : https://prove2.me/submissions/49a50a87-0048-46ce-9748-39c98daded1c

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSharedReportingLevels_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankSources_source_bounds

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.LightSharedReportingPair
end ThreeSum.LightSharedReportingPair
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SharedReportingBankSources
end ThreeSum.SharedReportingBankSources
namespace ThreeSum.SourceBandLayout
end ThreeSum.SourceBandLayout
namespace ThreeSum.SourceBandPartition
end ThreeSum.SourceBandPartition
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockForced
end ThreeSum1960614.Machine.ThreeSum.BlockForced
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
end ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightSharedReportingPair
end ThreeSum1960614.Machine.ThreeSum.LightSharedReportingPair
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandLayout
end ThreeSum1960614.Machine.ThreeSum.SourceBandLayout
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandPartition
end ThreeSum1960614.Machine.ThreeSum.SourceBandPartition
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

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
# Exact bridge from row-major machine masks to the block reporting query

The explicit coordinate equivalence sends the remaining blocks to a
contiguous suffix. Transport of finite subset sums identifies the machine's
Möbius value with the concrete forced-prefix count used by reporting.
-/

namespace ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.BlockIndexedQuery


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open scoped _root_.BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

































section Histograms

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]





theorem leftWeights_le_card {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (P : ℤ)
    (B : Finset β) (b : β → ℤ) (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h))) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftWeights o P B b S ≤ B.card := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftWeights
  split_ifs with ha
  · calc
      _ ≤ ∑ _j ∈ B, (1 : ℕ) := Finset.sum_le_sum (fun _ _ => by split_ifs <;> omega)
      _ = _ := by simp
  · omega

theorem rightWeights_le_card {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (P d : ℤ)
    (C : Finset γ) (c : γ → ℤ) (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h))) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightWeights o P d C c S ≤ C.card := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightWeights
  split_ifs with ha
  · calc
      _ ≤ ∑ _j ∈ C, (1 : ℕ) := Finset.sum_le_sum (fun _ _ => by split_ifs <;> omega)
      _ = _ := by simp
  · omega

theorem leftSource_abs_le {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ)
    (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (S : Finset (Fin (J*(464*h)))) : |_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource P B b q S| ≤ B.card := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource _root_.ThreeSum.SubsetTransport.reindex
  rw [Int.abs_natCast]
  exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftWeights_le_card (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) P B b _

theorem rightSource_abs_le {h J : ℕ} (P d : ℤ) (C : Finset γ) (c : γ → ℤ)
    (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (S : Finset (Fin (J*(464*h)))) : |_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource P d C c q S| ≤ C.card := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource _root_.ThreeSum.SubsetTransport.reindex
  rw [Int.abs_natCast]
  exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightWeights_le_card (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) P d C c _







end Histograms

end ThreeSum.BlockIndexedQuery

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

/-! # Exact finite original-position sources for real and padded bands -/

namespace ThreeSum.SourceBandPartition
open _root_.ThreeSum.SourceBandPartition


open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.SourceBandLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout











theorem source_card (n g i : ℕ) : (_root_.ThreeSum.SourceBandPartition.source n g i).card=_root_.ThreeSum.SourceBandLayout.len n g i := by
  simpa only [Fintype.card_fin,Fintype.card_coe] using (Fintype.card_congr (_root_.ThreeSum.SourceBandPartition.equiv n g i)).symm









end ThreeSum.SourceBandPartition

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Independent source bands and exact reuse for every decoded output -/

namespace ThreeSum.SharedReportingBankSources
open _root_.ThreeSum.SharedReportingBankSources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords










theorem source_pair {μ : ℕ → ℤ} {fB fC : ℕ → ℤ}
    {base NB NC g h J cut occ i j s : ℕ} {p shift : ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.Stored μ fB fC base NB NC g h J cut occ p shift)
    (hi : i < _root_.ThreeSum.SourceBandPairSlices.count NB NC g) (hj : j < _root_.ThreeSum.SourceBandPairSlices.count NB NC g)
    (hs : s < _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) :
    μ (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.leftCell base h J cut i s)=(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.leftBase base h J cut i s : ℤ) ∧
      μ (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.rightCell base h J cut j s)=(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.rightBase base h J cut j s : ℤ) ∧
      _root_.ThreeSum.LightZetaStages.StoredThrough μ (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.leftBase base h J cut i s) cut
        (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource p (_root_.ThreeSum.SourceBandPartition.source NB g i) (fun t : Fin NB => fB t.val)
          (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder.representative h J s)) (J*(464*h)) ∧
      _root_.ThreeSum.LightZetaStages.StoredThrough μ (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.rightBase base h J cut j s) cut
        (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource p shift (_root_.ThreeSum.SourceBandPartition.source NC g j) (fun t : Fin NC => fC t.val)
          (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder.representative h J s)) (J*(464*h)) :=
  ⟨(H.banks i hi s hs).headerLeft,(H.banks j hj s hs).headerRight,
    (H.banks i hi s hs).left,(H.banks j hj s hs).right⟩









end ThreeSum.SharedReportingBankSources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Retained source pointers and complete source families precede the bank end -/

namespace ThreeSum.SharedReportingBankSources
open _root_.ThreeSum.SharedReportingBankSources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding



theorem source_card_le (n g i : ℕ) : (_root_.ThreeSum.SourceBandPartition.source n g i).card ≤ g := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPartition.source_card]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.length_le n g i

theorem left_abs_le (p : ℤ) (NB g i h J s : ℕ) (fB : ℕ → ℤ)
    (S : Finset (Fin (J*(464*h)))) :
    |_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource p (_root_.ThreeSum.SourceBandPartition.source NB g i) (fun t : Fin NB => fB t.val)
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder.representative h J s) S| ≤ (g : ℤ) :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource_abs_le _ _ _ _ _).trans (Int.ofNat_le.mpr (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.source_card_le NB g i))

theorem right_abs_le (p shift : ℤ) (NC g i h J s : ℕ) (fC : ℕ → ℤ)
    (S : Finset (Fin (J*(464*h)))) :
    |_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource p shift (_root_.ThreeSum.SourceBandPartition.source NC g i) (fun t : Fin NC => fC t.val)
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder.representative h J s) S| ≤ (g : ℤ) :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource_abs_le _ _ _ _ _ _).trans (Int.ofNat_le.mpr (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.source_card_le NC g i))

end ThreeSum.SharedReportingBankSources

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingPair

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum.SharedReportingBankLevels
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources
set_option maxHeartbeats 2400000
set_option maxRecDepth 11000
section

theorem ThreeSum1960614.Machine.ThreeSum.LightSharedReportingPair.program_meets__implementation_1bcbd0defb {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ → ℤ} {fB fC : ℕ → ℤ}
    {header NB NC g h J occ s i j K record base d : ℕ} {p shift : ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.Stored μ fB fC header NB NC g h J (2*h*J) occ p shift)
    (hs : s < _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J)
    (hi : i < _root_.ThreeSum.SourceBandPairSlices.count NB NC g)
    (hj : j < _root_.ThreeSum.SourceBandPairSlices.count NB NC g)
    (hw : (lim.space : ℤ) ≤ lim.word) (hK : K ≤ _root_.ThreeSum.LightSwitchDepth.depth J+1)
    (hsource : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.finish header NB NC g h J (2*h*J) ≤ record)
    (hrecords : record+5*K ≤ base)
    (R : _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels.Resources lim base h J K g g (d+1)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingPair.program 65 d
      [h,J,K,_root_.ThreeSum.SourceBandBankData.first header,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span h J (2*h*J),s,i,j,
        _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localChoose h,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h,record,base] μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingPair.time h J K)
      (fun result ν => result=(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J K : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.Built ν record base h J K
          (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource p (_root_.ThreeSum.SourceBandPartition.source NB g i) (fun t : Fin NB => fB t.val) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder.representative h J s))
          (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource p shift (_root_.ThreeSum.SourceBandPartition.source NC g j) (fun t : Fin NC => fC t.val) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder.representative h J s)) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν record ∧ _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν base record (5*K)) := by
  have hleft := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.source_bounds (base := header) (cut := 2*h*J) hi hs
  have hright := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.source_bounds (base := header) (cut := 2*h*J) hj hs
  have hdata := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.source_pair H hi hj hs
  have hspace := R.space
  have hdepth := R.widthDepth
  have hstate := R.state
  have hbase : base ≤ lim.space := (Nat.le_add_right _ _).trans hspace
  have hleftAddr : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.leftCell header h J (2*h*J) i s < record := hleft.1.trans_le hsource
  have hrightAddr : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.rightCell header h J (2*h*J) j s < record := hright.2.1.trans_le hsource
  have hlNat : _root_.ThreeSum.SourceBandBankData.first header+i*_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span h J (2*h*J)+2*s < lim.space :=
    hleftAddr.trans_le (by omega)
  have hrNat : _root_.ThreeSum.SourceBandBankData.first header+j*_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span h J (2*h*J)+2*s+1 < lim.space :=
    hrightAddr.trans_le (by omega)
  have hlZ : (_root_.ThreeSum.SourceBandBankData.first header : ℤ)+(i : ℤ)*(_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span h J (2*h*J) : ℤ)+2*(s : ℤ) < (lim.space : ℤ) := by
    exact_mod_cast hlNat
  have hrZ : (_root_.ThreeSum.SourceBandBankData.first header : ℤ)+(j : ℤ)*(_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span h J (2*h*J) : ℤ)+2*(s : ℤ)+1 < (lim.space : ℤ) := by
    exact_mod_cast hrNat
  have hiNZ : (0 : ℤ) ≤ (i : ℤ)*(_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span h J (2*h*J) : ℤ) := by positivity
  have hjNZ : (0 : ℤ) ≤ (j : ℤ)*(_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span h J (2*h*J) : ℤ) := by positivity
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 65) (by rfl : program[65]?=some (body 64))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingPair.body _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingPair.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.leftCell header h J (2 * h * J) i s : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.leftCell, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.bankBase, _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.baseAt]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.leftCell, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.bankBase, _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.baseAt] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.leftCell, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.bankBase, _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.baseAt] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.rightCell header h J (2 * h * J) j s : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.rightCell, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.bankBase, _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.baseAt]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.rightCell, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.bankBase, _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.baseAt] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.rightCell, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.bankBase, _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.baseAt] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hc := (_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels.program_meets (d := d+1)
    (record := record) (base := base)
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource p (_root_.ThreeSum.SourceBandPartition.source NB g i) (fun t : Fin NB => fB t.val) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder.representative h J s))
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource p shift (_root_.ThreeSum.SourceBandPartition.source NC g j) (fun t : Fin NC => fC t.val) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder.representative h J s))
    hw hK hrecords hleftAddr hrightAddr (hleft.2.2.1.trans hsource) (hright.2.2.2.trans hsource) R
    (fun S _ => _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.left_abs_le p NB g i h J s fB S)
    (fun S _ => _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.right_abs_le p shift NC g j h J s fC S)
    hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingPair.body 64]
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
     on_goal -1 => (rintro result ν ⟨hresult, hbuilt, hkeep, hkeepBlock⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
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
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hresult]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hresult] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hresult] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  exact ⟨rfl,hbuilt,hkeep,hkeepBlock⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightSharedReportingPair.program_meets__implementation_1bcbd0defb) := (@ThreeSum1960614.Machine.ThreeSum.LightSharedReportingPair.program_meets__implementation_1bcbd0defb)

#print axioms solution
