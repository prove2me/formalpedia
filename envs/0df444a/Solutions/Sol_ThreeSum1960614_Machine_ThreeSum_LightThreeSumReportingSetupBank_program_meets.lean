-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupBank.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:00:42.337007+00:00
-- url     : https://prove2.me/submissions/84f45723-2c52-4cdd-9312-78474f288deb

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorPipelineData_Stored_of_kept
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorPipelineData_ordered
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSharedReportingHost_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankCosts_host_time_le
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_resources

namespace Filter
end Filter
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockSourceSharing
end ThreeSum.BlockSourceSharing
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.EncodedColorPipelineData
end ThreeSum.EncodedColorPipelineData
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter
namespace ThreeSum.LightThreeSumReportingSetupBank
end ThreeSum.LightThreeSumReportingSetupBank
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankResourceBounds
end ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum.SourceBandPairData
end ThreeSum.SourceBandPairData
namespace ThreeSum.SourceFiniteData
end ThreeSum.SourceFiniteData
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.ThreeSumColorBudgets
end ThreeSum.ThreeSumColorBudgets
namespace ThreeSum.ThreeSumReportingSetupData
end ThreeSum.ThreeSumReportingSetupData
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
end ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
namespace ThreeSum1960614.Machine.ThreeSum.ColorClassLists
end ThreeSum1960614.Machine.ThreeSum.ColorClassLists
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightClassFilter
end ThreeSum1960614.Machine.ThreeSum.LightClassFilter
namespace ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupBank
end ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupBank
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandPairData
end ThreeSum1960614.Machine.ThreeSum.SourceBandPairData
namespace ThreeSum1960614.Machine.ThreeSum.SourceFiniteData
end ThreeSum1960614.Machine.ThreeSum.SourceFiniteData
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets
end ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
end ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
namespace ThreeSum1960614.Machine.ThreeSum.TrimScales
end ThreeSum1960614.Machine.ThreeSum.TrimScales
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

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













/-- Reading a cell of a segment, with a default value for the list. -/
theorem Seg.getD (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) {i : ℕ} (hi : i < l.length) (d : ℤ) : μ (a + i) = l.getD i d := by
  rw [h i hi, List.getD_eq_getElem _ _ hi]

































































end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact sharing of source transforms and the encoder ledger

Source stages are indexed by a source band and an occurrence vector. The
output subset and the three-valued A lift do not enter the source function.
Compact table and zeta charges below match the existing `encoderCount`
without introducing a factor for all complete global outputs.
-/

namespace ThreeSum.BlockSourceSharing
open _root_.ThreeSum.BlockSourceSharing


open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds















theorem cutoff_eq (n : ℕ) :
    2*_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) = _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize _root_.ThreeSum.Scales.microSize _root_.ThreeSum.Scales.microHalf
  ring

















end ThreeSum.BlockSourceSharing

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

/-! # Two retained original-band catalogs and one shared empty histogram -/

namespace ThreeSum.SourceBandPairData
open _root_.ThreeSum.SourceBandPairData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition






theorem work_ge (base n g m : ℕ) : base ≤ _root_.ThreeSum.SourceBandLayout.work base n g m := by
  unfold _root_.ThreeSum.SourceBandLayout.work _root_.ThreeSum.SourceBandLayout.hist _root_.ThreeSum.SourceBandLayout.data
  omega

theorem ordered (base NL NR g m : ℕ) :
    _root_.ThreeSum.SourceBandPairData.leftBase base ≤ _root_.ThreeSum.SourceBandPairData.rightBase base NL g m ∧
    _root_.ThreeSum.SourceBandPairData.rightBase base NL g m ≤ _root_.ThreeSum.SourceBandPairData.zeroBase base NL NR g m ∧
    _root_.ThreeSum.SourceBandPairData.zeroBase base NL NR g m < _root_.ThreeSum.SourceBandPairData.next base NL NR g m := by
  exact ⟨_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.work_ge _ _ _ _,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.work_ge _ _ _ _,by unfold _root_.ThreeSum.SourceBandPairData.next; omega⟩















end ThreeSum.SourceBandPairData

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
# Polynomial limits for the actual shared reporting host

The finite word, cell, and depth formulas are bounded at every input size.
The resulting `Need` includes the complete executed host, while its time
bound remains the exact shared-box budget proved separately.
-/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.Filter
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open scoped _root_.Topology

set_option maxHeartbeats 1200000
set_option maxRecDepth 14000

noncomputable section



















theorem resources_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {n U free NB NC d : ℕ}
    (hB : NB ≤ n) (hC : NC ≤ n) (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.need n U).Ok lim free d) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingHost.Resources lim free (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
      NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) d :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.resources hB hC hok.cells hok.word hok.depth

end
end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Keep the complete finite source catalog below its exact returned end -/

namespace ThreeSum.SourceFiniteData
open _root_.ThreeSum.SourceFiniteData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

theorem source_ends (base NL NR g h J cut : ℕ) :
    base+3 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.finish base NL NR g h J cut ∧
    _root_.ThreeSum.SourceBandPairData.next (_root_.ThreeSum.LightSourceControlsHost.sourceBase base) NL NR g
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.finish base NL NR g h J cut ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.bankHeader (_root_.ThreeSum.LightSourceControlsHost.sourceBase base) NL NR g h J+5 ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.finish base NL NR g h J cut := by
  have ho := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.ordered (_root_.ThreeSum.LightSourceControlsHost.sourceBase base)
    NL NR g (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.finish _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.finish _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.finish
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.baseAt _root_.ThreeSum.SourceBandBankData.first _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.bankHeader
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.occurrenceBase _root_.ThreeSum.LightSourceControlsHost.sourceBase
  unfold _root_.ThreeSum.SourceBandPairData.leftBase _root_.ThreeSum.LightSourceControlsHost.sourceBase at ho
  omega



end ThreeSum.SourceFiniteData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Executed shared catalogs with proved polynomial limits and exact time -/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

theorem program_meets {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ → ℤ} {fB fC : ℕ → ℤ}
    {n U controls pairHeader bankHeader free NB NC occ p m d : ℕ} {shift : ℤ}
    (hB : NB ≤ n) (hC : NC ≤ n)
    (Hcontrol : _root_.ThreeSum1960614.Machine.Light.Seg μ controls (_root_.ThreeSum1960614.Machine.ThreeSum.SourceControlLayout.values (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (2*_root_.ThreeSum.SharedReportingBankResourceBounds.half n*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)))
    (Hpair : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.Stored μ fB fC pairHeader NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) p m shift)
    (Hbank : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.Stored μ fB fC bankHeader NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
      (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (2*_root_.ThreeSum.SharedReportingBankResourceBounds.half n*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) occ (p : ℤ) shift)
    (hcontrol : controls+3 ≤ free) (hpair : pairHeader+8 ≤ free)
    (hocc : occ+_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n ≤ bankHeader)
    (hsource : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.finish bankHeader NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
      (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (2*_root_.ThreeSum.SharedReportingBankResourceBounds.half n*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) ≤ free)
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.need n U).Ok lim free d) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingHost.program 74 d
      [_root_.ThreeSum.SharedReportingBankResourceBounds.half n,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n,controls,pairHeader,bankHeader,free] μ (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.budget n)
      (fun result ν => result=(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish free (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
          NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.Stored ν free (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
          NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) fB fC (p : ℤ) shift ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν free) :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingHost.program_meets Hcontrol Hpair Hbank hok.space
    hcontrol hpair hocc hsource (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.resources_of_ok hB hC hok)).mono_time
      (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.host_time_le hB hC)

end ThreeSum.SharedReportingBankResourceBounds

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















theorem prefix_le_report (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    free+8 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC := by
  obtain ⟨_,hf,hc,_,hs,_⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.ordered free n A B C hsA hsB hsC
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase
  omega





end ThreeSum.ThreeSumReportingSetupData

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupBank

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
set_option maxHeartbeats 2100000
set_option maxRecDepth 14000
section

theorem ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupBank.program_meets__implementation_f4ddcb6ef0 {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ} {μ : ℕ → ℤ} {free n params U : ℕ}
    {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (Hparams : _root_.ThreeSum1960614.Machine.Light.Seg μ params (_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values n)) (hparams : params+19 ≤ free)
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.need n U).Ok lim
      (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC) (d+1)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupBank.program 75 d [n,params,free,_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC]
      μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupBank.time n) (fun r ν => r=(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored ν free n color x A B C hsA hsB hsC ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.Catalog ν free n A B C hsA hsB hsC ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC)) := by
  let out := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC
  let report := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC
  let control := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC
  let pair := _root_.ThreeSum.LightSourceControlsHost.sourceBase control
  let bank := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.bankHeader free n A B C hsA hsB hsC
  let h := _root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)
  let J := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)
  obtain ⟨_,hB,hC⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.normalized_lengths H
  have R := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.resources_of_ok hB hC hok
  have hw := hok.space
  have hd : d < lim.depth := by have hh := hok.depth; omega
  have hreport : report+9 ≤ lim.space := by
    have hh := (le_max_left _ _).trans R.space
    change report+9+_root_.ThreeSum.LightPascal.tableSize (464*h) ≤ lim.space at hh
    omega
  have hprefix := (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.prefix_le_report free n A B C hsA hsB hsC).1
  change free+8 ≤ report at hprefix
  obtain ⟨_,_,_,_,hcontrol,hbank⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.ordered free n A B C hsA hsB hsC
  change control+3 ≤ out at hcontrol
  change bank+5 ≤ out at hbank
  have hpairs := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.ordered pair B.length C.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J)
  obtain ⟨_,hpairEnd,_⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteData.source_ends control B.length C.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) h J (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)
  change _root_.ThreeSum.SourceBandPairData.next pair B.length C.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) ≤ out at hpairEnd
  have hpair : pair+8 ≤ out := by
    unfold _root_.ThreeSum.SourceBandPairData.leftBase at hpairs
    omega
  have hHWord : (h : ℤ) ≤ lim.word := by
    have hh : h ≤ 2^(464*h+1) :=
      (Nat.lt_two_pow_self (n := h)).le.trans (Nat.pow_le_pow_right (by decide) (by omega))
    exact (Int.ofNat_le.mpr hh).trans R.powers
  have hJWord : (J : ℤ) ≤ lim.word := by
    apply (Int.ofNat_le.mpr (show J ≤ _root_.ThreeSum.LightSwitchDepth.word J by unfold _root_.ThreeSum.LightSwitchDepth.word; omega)).trans R.depthWord
  have hcut : 2*h*J=_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.cutoff_eq n
  have controls := H.sources.controls
  have banks := H.sources.banks
  rw [← hcut] at controls banks
  obtain ⟨_,_,_,readControl,readBank,readReport,_,_⟩ := H.heads_read
  change μ (out+3)=(control : ℤ) at readControl
  change μ (out+4)=(bank : ℤ) at readBank
  change μ (out+5)=(report : ℤ) at readReport
  obtain ⟨_,readH,readJ,_,_,_,_⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorParameterData.reads Hparams
  change μ (params+1)=(h : ℤ) at readH
  change μ (params+3)=(J : ℤ) at readJ
  have par1 : ((params : ℤ)+1).toNat=params+1 := by omega
  have par3 : ((params : ℤ)+3).toNat=params+3 := by omega
  have out3 : ((out : ℤ)+3).toNat=out+3 := by omega
  have out4 : ((out : ℤ)+4).toNat=out+4 := by omega
  have out5 : ((out : ℤ)+5).toNat=out+5 := by omega
  have outReport : out+8=report := rfl
  change _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupBank.program 75 d [n,params,free,out] μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupBank.time n) _
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 75) (by rfl : program[75]?=some (body 74))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupBank.body _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupBank.time
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
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readH, par1] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readH, par1] <;> omega)
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
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readJ, par3] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readJ, par3] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (control : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readControl, out3]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readControl, out3] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readControl, out3] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (pair : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightSourceControlsHost.sourceBase, pair]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightSourceControlsHost.sourceBase, pair] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightSourceControlsHost.sourceBase, pair] <;> omega)
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
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readBank, out4] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readBank, out4] <;> omega)
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
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readReport, out5]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readReport, out5] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readReport, out5] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hcall := (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.program_meets (d := d+1) (μ := μ)
    (controls := control) (pairHeader := pair) (bankHeader := bank) (free := report)
    hB hC controls H.sources.buckets banks (by omega) (by omega) le_rfl
    (by change _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.finish bank B.length C.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) h J (2*h*J) ≤ report
        rw [hcut]
        change out ≤ report
        omega) hok).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupBank.body 74]
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hcall _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hcall ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.SharedReportingBankResourceBounds.half, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks, h, J]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.SharedReportingBankResourceBounds.half, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks, h, J] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.SharedReportingBankResourceBounds.half, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks, h, J] <;> omega)
     on_goal -1 => (rintro result ν ⟨hresult, hcatalog, hkeep⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  exact ⟨hresult,H.of_kept hkeep le_rfl,hcatalog,hkeep⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupBank.program_meets__implementation_f4ddcb6ef0) := (@ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupBank.program_meets__implementation_f4ddcb6ef0)

#print axioms solution
