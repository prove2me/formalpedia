-- Prove2me | solution 2 for ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDecodeAccess.program_meets_fits
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T08:56:30.869455+00:00
-- url     : https://prove2.me/submissions/61179333-0230-4494-89d7-7ba24270e56d

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightCoverKeyData_Stored_of_kept
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingWantedAccess_program_meets_fits
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightWantedDecode_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankHeader_Stored_of_kept
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SourceBandBankData_Stored_of_kept
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SourceBandPairData_Stored_of_kept

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.LightReportingWantedAccess
end ThreeSum.LightReportingWantedAccess
namespace ThreeSum.LightReportingWantedDecodeAccess
end ThreeSum.LightReportingWantedDecodeAccess
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LightWantedDecode
end ThreeSum.LightWantedDecode
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.OutputDecodeOccurrenceCode
end ThreeSum.OutputDecodeOccurrenceCode
namespace ThreeSum.OutputDecodeOrder
end ThreeSum.OutputDecodeOrder
namespace ThreeSum.ReportingHostRelocation
end ThreeSum.ReportingHostRelocation
namespace ThreeSum.ReportingHostSourceSelection
end ThreeSum.ReportingHostSourceSelection
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
end ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
namespace ThreeSum1960614.Machine.ThreeSum.BandEnumeration
end ThreeSum1960614.Machine.ThreeSum.BandEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.BandRawA
end ThreeSum1960614.Machine.ThreeSum.BandRawA
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWantedAccess
end ThreeSum1960614.Machine.ThreeSum.LightReportingWantedAccess
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDecodeAccess
end ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDecodeAccess
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
end ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightWantedDecode
end ThreeSum1960614.Machine.ThreeSum.LightWantedDecode
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
end ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelection
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelection
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































theorem cells_length (rs : List _root_.ThreeSum.BandCandidateRows.Record) : (_root_.ThreeSum.BandCandidateRows.cells rs).length=4*rs.length := by
  induction rs with
  | nil => simp [_root_.ThreeSum.BandCandidateRows.cells]
  | cons r rs ih => simp only [_root_.ThreeSum.BandCandidateRows.cells,List.flatMap_cons,List.length_append,_root_.ThreeSum.BandCandidateRows.Record.cells,
      List.length_cons,List.length_nil] at *; omega























end ThreeSum.BandCandidateRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original-input histograms give the exact independently trimmed sources

The histogram keys retain the first modular reduction and the signed carry
offset. Looking up the endpoint's final residue therefore counts precisely
the original divisibility condition in `BlockEncoding`. An explicit finite
enumeration accounts for every original input incidence once.
-/

namespace ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.BlockSourceEncoding


open _root_.Finset
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightSourceResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
open scoped _root_.BigOperators

set_option maxHeartbeats 1000000









theorem modulus_pos (h J : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J := pow_pos (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h) J



section OriginalSources

variable {β : Type*} [DecidableEq β]





end OriginalSources

end ThreeSum.BlockSourceEncoding

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Occurrence-only source-bank indices, with first block most significant -/

namespace ThreeSum.OutputDecodeOccurrenceCode
open _root_.ThreeSum.OutputDecodeOccurrenceCode


open _root_.ThreeSum.OutputDecodeOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding

set_option maxHeartbeats 1500000



theorem last_lt {T M : ℕ} (hT : 0 < T) (hM : 0 < M) (k : ℕ) :
    (k%(T*M))/M < T :=
  (Nat.div_lt_iff_lt_mul hM).mpr (Nat.mod_lt _ (Nat.mul_pos hT hM))

theorem code_lt {T M : ℕ} (hT : 0 < T) (hM : 0 < M) (J k : ℕ) : _root_.ThreeSum.OutputDecodeOccurrenceCode.code T M J k < T^J := by
  induction J generalizing k with
  | zero => simp [_root_.ThreeSum.OutputDecodeOccurrenceCode.code]
  | succ J ih =>
    have hm := Nat.mul_le_mul_left T (show _root_.ThreeSum.OutputDecodeOccurrenceCode.code T M J (k/(T*M))+1 ≤ T^J by exact ih _)
    have hd := _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode.last_lt hT hM k
    simp only [Nat.mul_add,Nat.mul_one] at hm
    rw [_root_.ThreeSum.OutputDecodeOccurrenceCode.code,pow_succ']
    omega









end ThreeSum.OutputDecodeOccurrenceCode

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








































theorem ownerLabels_length (ls : List _root_.ThreeSum.BandRawA.Label) : (_root_.ThreeSum.BandRawA.ownerLabels ls).length=ls.length := List.length_map ..
theorem positionLabels_length (ls : List _root_.ThreeSum.BandRawA.Label) : (_root_.ThreeSum.BandRawA.positionLabels ls).length=ls.length := List.length_map ..



















end ThreeSum.BandRawA

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Decode an actual emitted wanted-pair cell

The host loads the two physical indices, splits the left index into its
incidence position and lift, and decodes the right index into the original
occurrence and Q-mask rows. Its four-cell header retains both source labels
and the occurrence-only bank index. Division is the verified binary routine.
-/

namespace ThreeSum.LightWantedDecode
open _root_.ThreeSum.LightWantedDecode


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000













variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {pairs slot N h J masks dst work i j V : ℕ}







theorem program_meets
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+3 < lim.depth)
    (hN : 0 < N) (hi : i ≤ V) (hj : j ≤ V) (hkey : j < _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h^J)
    (hpairs : pairs+2*slot+2 ≤ dst)
    (hmask : masks+_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h ≤ dst) (hsep : dst+4+J+J ≤ work)
    (hspace : _root_.ThreeSum.LightWantedDecode.space work V ≤ lim.space) (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.word V N h J : ℤ) ≤ lim.word)
    (hleft : μ (pairs+2*slot)=(i : ℤ)) (hright : μ (pairs+2*slot+1)=(j : ℤ))
    (hread : ∀ s < _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h,
      μ (masks+s)=(_root_.ThreeSum.LocalMaskGraph.maskAt (464*h) (2*h) s : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.program 4 d
      [pairs,slot,N,J,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h,_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h,masks,dst,work] μ (_root_.ThreeSum.LightWantedDecode.time J V)
      (fun r ν =>
        r=(_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J j : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.Stored ν dst N h J i j ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν dst) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.meets (pDecode := 0) ⟨1,2,3,rfl,rfl,rfl,rfl⟩ rfl
    hw hd hN hi hj hkey hpairs hmask hsep hspace hword hleft hright hread



end ThreeSum.LightWantedDecode

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # The three retained parallel arrays of A-value incidences -/

namespace ThreeSum.BandRawA
open _root_.ThreeSum.BandRawA


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows

set_option maxHeartbeats 1400000













theorem Stored.of_kept {μ ν : ℕ → ℤ} {vals owners positions fr : ℕ}
    {f : ℕ → ℤ} {ls : List _root_.ThreeSum.BandRawA.Label} (H : _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.Stored μ vals owners positions f ls)
    (hk : _root_.ThreeSum1960614.Machine.Light.Kept μ ν fr) (hv : vals+ls.length ≤ fr)
    (ho : owners+ls.length ≤ fr) (hp : positions+ls.length ≤ fr) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.Stored ν vals owners positions f ls :=
  ⟨H.valueRows.of_kept hk (by simpa only [_root_.ThreeSum.BandRawA.values_length] using hv),
    H.ownerRows.of_kept hk (by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.ownerLabels_length] using ho),
    H.positionRows.of_kept hk (by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.positionLabels_length] using hp)⟩

end ThreeSum.BandRawA

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Decode and select one physical wanted slot

The actual emitted pair is decoded before selecting the physical A owner,
both original bands, the retained occurrence sources and the shared catalog
row. The original decoded Q rows survive the selection for mask packing.
-/

namespace ThreeSum.LightReportingWantedDecodeAccess
open _root_.ThreeSum.LightReportingWantedDecodeAccess


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
open _root_.ThreeSum.ReportingHostSourceSelection
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelection
open _root_.ThreeSum.LightReportingWantedAccess
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedAccess

set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
set_option linter.unusedVariables false







theorem decoded_of_kept {μ ν : ℕ→ℤ} {dst N h J i j stop : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.Stored μ dst N h J i j)
    (hk : _root_.ThreeSum1960614.Machine.Light.Kept μ ν stop) (he : dst+4+J+J≤ stop) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.Stored ν dst N h J i j := by
  refine ⟨?_,?_,?_,?_,⟨?_,?_⟩⟩
  · exact (hk _ (by omega)).trans H.position
  · exact (hk _ (by omega)).trans H.liftIndex
  · exact (hk _ (by omega)).trans H.outputIndex
  · exact (hk _ (by omega)).trans H.bankIndex
  · intro t
    exact (hk _ (by omega)).trans (H.rows.occurrences t)
  · intro t
    exact (hk _ (by omega)).trans (H.rows.masks t)





end ThreeSum.LightReportingWantedDecodeAccess

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightReportingWantedDecodeAccess
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDecodeAccess

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
open _root_.ThreeSum.ReportingHostSourceSelection
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelection
open _root_.ThreeSum.LightReportingWantedAccess
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedAccess
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
set_option linter.unusedVariables false
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDecodeAccess.program_meets_fits__implementation_5b74ddf6d7 {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ}
    {n g vals owners positions records pair bank cover NB NC p h J cut occ srcB srcC report decoded dst work d : ℕ}
    {pairs slot i j V masks : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record} {shift : ℤ}
    (HA : _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.Stored μ vals owners positions fA (_root_.ThreeSum.BandRawA.items n g rs))
    (HR : _root_.ThreeSum1960614.Machine.Light.Seg μ records (_root_.ThreeSum.BandCandidateRows.cells rs)) (hiRaw : i<3*(_root_.ThreeSum.BandRawA.items n g rs).length)
    (hjKey : j<_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h^J) (hiV : i≤V) (hjV : j≤V)
    (HP : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.Stored μ fB fC pair NB NC g p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) shift)
    (HB : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.Stored μ fB fC bank NB NC g h J cut occ (p : ℤ) shift)
    (HC : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.Stored μ cover h J)
    (HQ : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.Stored μ report h J NB NC g fB fC (p : ℤ) shift)
    (hi : (_root_.ThreeSum.BandRawA.ownerRecord n g rs (i%(_root_.ThreeSum.BandRawA.items n g rs).length)).b<_root_.ThreeSum.BandPartition.size NB g)
    (hj : (_root_.ThreeSum.BandRawA.ownerRecord n g rs (i%(_root_.ThreeSum.BandRawA.items n g rs).length)).c<_root_.ThreeSum.BandPartition.size NC g)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+4<lim.depth)
    (hvals : vals+(_root_.ThreeSum.BandRawA.items n g rs).length≤decoded)
    (howners : owners+(_root_.ThreeSum.BandRawA.items n g rs).length≤decoded)
    (hpositions : positions+(_root_.ThreeSum.BandRawA.items n g rs).length≤decoded)
    (hrecords : records+4*rs.length≤decoded)
    (hsrcB : srcB+NB≤decoded) (hsrcC : srcC+NC≤decoded)
    (hpair : _root_.ThreeSum.SourceBandPairData.next pair NB NC g (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J)≤decoded)
    (hbank : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.finish bank NB NC g h J cut≤decoded)
    (hocc : occ+_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J*J≤bank)
    (hcover : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd cover h J≤decoded)
    (hreport : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish report h J NB NC g≤decoded)
    (hdecoded : decoded+4+J+J≤dst) (hwork : dst+20≤work)
    (hpairs : pairs+2*slot+2≤decoded) (hmasks : masks+_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h≤decoded)
    (hleft : μ (pairs+2*slot)=(i : ℤ)) (hright : μ (pairs+2*slot+1)=(j : ℤ))
    (hread : ∀ s<_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h,
      μ (masks+s)=(_root_.ThreeSum.LocalMaskGraph.maskAt (464*h) (2*h) s : ℤ))
    (hdecoderSpace : _root_.ThreeSum.LightWantedDecode.space work V≤lim.space)
    (hdecoderWord : (_root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.word V (_root_.ThreeSum.BandRawA.items n g rs).length h J : ℤ)≤lim.word)
    (hspace : _root_.ThreeSum.ReportingHostSourceSelection.Fits
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedAccess.selection n g rs (i%(_root_.ThreeSum.BandRawA.items n g rs).length) pair bank cover NB NC h J cut occ
        (_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J j))
      pair bank cover srcB srcC
      (_root_.ThreeSum.BandRawA.ownerRecord n g rs (i%(_root_.ThreeSum.BandRawA.items n g rs).length)).b
      (_root_.ThreeSum.BandRawA.ownerRecord n g rs (i%(_root_.ThreeSum.BandRawA.items n g rs).length)).c
      (_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J j) J (dst+5) lim.space)
    (hvalue : |fA (_root_.ThreeSum.BandRawA.labelAt n g rs (i%(_root_.ThreeSum.BandRawA.items n g rs).length)).position|≤lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDecodeAccess.program 9 d
      [pairs,slot,(_root_.ThreeSum.BandRawA.items n g rs).length,J,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h,_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h,masks,decoded,work,
        vals,owners,records,pair,bank,cover,srcB,srcC,report,dst]
      μ (_root_.ThreeSum.LightReportingWantedDecodeAccess.time J V)
      (fun result ν => result=(dst : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.Stored ν decoded (_root_.ThreeSum.BandRawA.items n g rs).length h J i j ∧
        _root_.ThreeSum1960614.Machine.Light.Seg ν dst (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedAccess.record fA n g rs (i%(_root_.ThreeSum.BandRawA.items n g rs).length) pair bank cover NB NC h J cut occ
          (_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J j) srcB srcC report) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν decoded) := by
  have hn : 0<(_root_.ThreeSum.BandRawA.items n g rs).length := by omega
  let idx := i%(_root_.ThreeSum.BandRawA.items n g rs).length
  let code := _root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J j
  have hidx : idx<(_root_.ThreeSum.BandRawA.items n g rs).length := Nat.mod_lt _ hn
  have hk : code<_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J :=
    _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode.code_lt (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.schedule_pos h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount_pos h) J j
  have hdst : decoded≤dst := by omega
  have hout : dst+20≤lim.space := by have hh := hspace.output; omega
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 9) (by rfl : program[9]?=some (body 4 8))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDecodeAccess.body _root_.ThreeSum.LightReportingWantedDecodeAccess.time
  have hdecode := (_root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.program_meets (d := d+1) (N := (_root_.ThreeSum.BandRawA.items n g rs).length)
    hw (by omega) hn hiV hjV hjKey hpairs hmasks (by omega)
    hdecoderSpace hdecoderWord hleft hright hread).append
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedAccess.program.map (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate 5) ++ [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDecodeAccess.body 4 8])
  change _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDecodeAccess.program 4 (d+1) _ μ _ _ at hdecode
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hdecode _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hdecode ?_ ?_ ?_ ?_
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
     on_goal -1 => (rintro bankCode μ₁ ⟨hcode, hdecoded₁, hkeep₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hposition : μ₁ decoded=(idx : ℤ) := hdecoded₁.position
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (idx : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hposition]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hposition] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hposition] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have HA₁ := HA.of_kept hkeep₁ hvals howners hpositions
  have HR₁ := HR.of_kept hkeep₁ (by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.cells_length] using hrecords)
  have HP₁ := HP.of_kept (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus_pos h J) hkeep₁ hpair
  have HB₁ := HB.of_kept hkeep₁ hocc hbank
  have HC₁ := HC.of_kept (fun a ha => hkeep₁ a (ha.trans_le hcover))
  have HQ₁ := HQ.of_kept hkeep₁ hreport
  have haccess := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedAccess.program_meets_fits (μ := μ₁) (d := d+1) (dst := dst)
    HA₁ HR₁ hidx HP₁ HB₁ HC₁ HQ₁ hi hj hk hw (by omega)
    (hvals.trans hdst) (howners.trans hdst) (hrecords.trans hdst)
    (hsrcB.trans hdst) (hsrcC.trans hdst) (hpair.trans hdst) (hbank.trans hdst) hocc
    (hcover.trans hdst) (hreport.trans hdst) hspace hvalue
  have haccessRun := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.meets haccess _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.program).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDecodeAccess.body 4 8]
  change _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDecodeAccess.program 8 (d+1) _ μ₁ 8100 _ at haccessRun
  have hcode' : bankCode=(code : ℤ) := hcode
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (haccessRun _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen haccessRun ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcode']
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hcode'] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcode'] <;> omega)
     on_goal -1 => (rintro result ν ⟨hresult, hselected, hkeep₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  exact ⟨hresult,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDecodeAccess.decoded_of_kept hdecoded₁ hkeep₂ hdecoded,hselected,
    fun a ha => (hkeep₂ a (ha.trans_le hdst)).trans (hkeep₁ a ha)⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDecodeAccess.program_meets_fits__implementation_5b74ddf6d7) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDecodeAccess.program_meets_fits__implementation_5b74ddf6d7)

#print axioms solution
