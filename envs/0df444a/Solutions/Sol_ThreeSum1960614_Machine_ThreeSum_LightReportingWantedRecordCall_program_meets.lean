-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordCall.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T10:03:10.32521+00:00
-- url     : https://prove2.me/submissions/e4a72148-aa56-435d-9d57-1da13f1518de

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
import Mathlib.Tactic.ClearExclamation

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightReportingWantedRecordCall
end ThreeSum.LightReportingWantedRecordCall
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.ReportingHostWantedControls
end ThreeSum.ReportingHostWantedControls
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordCall
end ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordCall
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
end ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
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













/-- Reading a cell of a segment, with a default value for the list. -/
theorem Seg.getD (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) {i : ℕ} (hi : i < l.length) (d : ℤ) : μ (a + i) = l.getD i d := by
  rw [h i hi, List.getD_eq_getElem _ _ hi]

































































end Light

end

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

set_option maxHeartbeats 1500000











@[simp] theorem modulus_cast (h J : ℕ) : (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J : ℤ) = _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus,Nat.cast_pow]

section OriginalSources

variable {β : Type*} [DecidableEq β]





end OriginalSources

end ThreeSum.BlockSourceEncoding

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordCall

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum.ReportingHostWantedControls
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls
set_option diagnostics true
set_option maxHeartbeats 1500000
set_option maxRecDepth 24000
set_option linter.unusedVariables false
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordCall.program_meets__implementation_2a8fd7c113 {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ→ℤ} {S : _root_.ThreeSum.ReportingHostWantedControls.Selection} {L : _root_.ThreeSum.ReportingHostWantedLayout.Layout}
    {selectionHeader layoutHeader cover counter h J K d T : ℕ} {Q : ℤ→(ℕ→ℤ)→Prop}
    (H : _root_.ThreeSum1960614.Machine.Light.Seg μ selectionHeader (_root_.ThreeSum.ReportingHostWantedControls.record S)) (HL : _root_.ThreeSum1960614.Machine.Light.SegN μ layoutHeader (_root_.ThreeSum.ReportingHostWantedLayout.values L))
    (hprime : μ (cover+6)=(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ))
    (hcap : μ (cover+7)=(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h : ℤ))
    (hw : (lim.space : ℤ)≤lim.word) (hd : d<lim.depth)
    (hs : _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordCall.space selectionHeader layoutHeader cover counter h J K≤lim.space)
    (hselected : ∀ x∈_root_.ThreeSum.ReportingHostWantedControls.record S, |x|≤lim.word)
    (hlayout : ∀ x∈_root_.ThreeSum.ReportingHostWantedLayout.values L, x≤lim.space)
    (hreport : _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWanted.program 137 (d+1)
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls.arguments S L layoutHeader cover counter h J K) μ T Q) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordCall.program 138 d
      [selectionHeader,layoutHeader,h,J,K,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J,cover,counter]
      μ (T+4000) Q := by
  have hs0 : μ (((selectionHeader : ℤ)+0).toNat)=S.av := by
    rw [show ((selectionHeader : ℤ)+0).toNat=selectionHeader+0 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedControls.record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 0) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record]) 0
  have hs1 : μ (((selectionHeader : ℤ)+1).toNat)=(S.owner : ℤ) := by
    rw [show ((selectionHeader : ℤ)+1).toNat=selectionHeader+1 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedControls.record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 1) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record]) 0
  have hs2 : μ (((selectionHeader : ℤ)+2).toNat)=(S.bandB : ℤ) := by
    rw [show ((selectionHeader : ℤ)+2).toNat=selectionHeader+2 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedControls.record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 2) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record]) 0
  have hs3 : μ (((selectionHeader : ℤ)+3).toNat)=(S.bandC : ℤ) := by
    rw [show ((selectionHeader : ℤ)+3).toNat=selectionHeader+3 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedControls.record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 3) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record]) 0
  have hs4 : μ (((selectionHeader : ℤ)+4).toNat)=(S.catalog : ℤ) := by
    rw [show ((selectionHeader : ℤ)+4).toNat=selectionHeader+4 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedControls.record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 4) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record]) 0
  have hs5 : μ (((selectionHeader : ℤ)+5).toNat)=(S.srcL : ℤ) := by
    rw [show ((selectionHeader : ℤ)+5).toNat=selectionHeader+5 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4 hs5); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedControls.record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 5) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record]) 0
  have hs6 : μ (((selectionHeader : ℤ)+6).toNat)=(S.srcR : ℤ) := by
    rw [show ((selectionHeader : ℤ)+6).toNat=selectionHeader+6 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4 hs5 hs6); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedControls.record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 6) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record]) 0
  have hs7 : μ (((selectionHeader : ℤ)+7).toNat)=(S.offsetsL : ℤ) := by
    rw [show ((selectionHeader : ℤ)+7).toNat=selectionHeader+7 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedControls.record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 7) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record]) 0
  have hs8 : μ (((selectionHeader : ℤ)+8).toNat)=(S.flatL : ℤ) := by
    rw [show ((selectionHeader : ℤ)+8).toNat=selectionHeader+8 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedControls.record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 8) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record]) 0
  have hs9 : μ (((selectionHeader : ℤ)+9).toNat)=(S.offsetsR : ℤ) := by
    rw [show ((selectionHeader : ℤ)+9).toNat=selectionHeader+9 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedControls.record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 9) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record]) 0
  have hs10 : μ (((selectionHeader : ℤ)+10).toNat)=(S.flatR : ℤ) := by
    rw [show ((selectionHeader : ℤ)+10).toNat=selectionHeader+10 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedControls.record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 10) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record]) 0
  have hs11 : μ (((selectionHeader : ℤ)+11).toNat)=(S.NL : ℤ) := by
    rw [show ((selectionHeader : ℤ)+11).toNat=selectionHeader+11 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedControls.record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 11) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record]) 0
  have hs12 : μ (((selectionHeader : ℤ)+12).toNat)=(S.NR : ℤ) := by
    rw [show ((selectionHeader : ℤ)+12).toNat=selectionHeader+12 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedControls.record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 12) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record]) 0
  have hs13 : μ (((selectionHeader : ℤ)+13).toNat)=(S.baseL : ℤ) := by
    rw [show ((selectionHeader : ℤ)+13).toNat=selectionHeader+13 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedControls.record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 13) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record]) 0
  have hs14 : μ (((selectionHeader : ℤ)+14).toNat)=(S.baseR : ℤ) := by
    rw [show ((selectionHeader : ℤ)+14).toNat=selectionHeader+14 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedControls.record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 14) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record]) 0
  have hs15 : μ (((selectionHeader : ℤ)+15).toNat)=(S.occ : ℤ) := by
    rw [show ((selectionHeader : ℤ)+15).toNat=selectionHeader+15 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedControls.record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 15) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record]) 0
  have hs16 : μ (((selectionHeader : ℤ)+16).toNat)=(S.maps : ℤ) := by
    rw [show ((selectionHeader : ℤ)+16).toNat=selectionHeader+16 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedControls.record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 16) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record]) 0
  have hs17 : μ (((selectionHeader : ℤ)+17).toNat)=(S.candidates : ℤ) := by
    rw [show ((selectionHeader : ℤ)+17).toNat=selectionHeader+17 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedControls.record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 17) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record]) 0
  have hs18 : μ (((selectionHeader : ℤ)+18).toNat)=(S.histL : ℤ) := by
    rw [show ((selectionHeader : ℤ)+18).toNat=selectionHeader+18 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedControls.record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 18) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record]) 0
  have hs19 : μ (((selectionHeader : ℤ)+19).toNat)=(S.histR : ℤ) := by
    rw [show ((selectionHeader : ℤ)+19).toNat=selectionHeader+19 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedControls.record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 19) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record]) 0
  have hl0 : μ (((layoutHeader : ℤ)+0).toNat)=(L.root : ℤ) := by
    rw [show ((layoutHeader : ℤ)+0).toNat=layoutHeader+0 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hl0); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedLayout.values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 0) (by simp [_root_.ThreeSum.ReportingHostWantedLayout.values]) 0
  have hl1 : μ (((layoutHeader : ℤ)+1).toNat)=(L.masks : ℤ) := by
    rw [show ((layoutHeader : ℤ)+1).toNat=layoutHeader+1 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hl0 hl1); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedLayout.values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 1) (by simp [_root_.ThreeSum.ReportingHostWantedLayout.values]) 0
  have hl2 : μ (((layoutHeader : ℤ)+2).toNat)=(L.childL : ℤ) := by
    rw [show ((layoutHeader : ℤ)+2).toNat=layoutHeader+2 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hl0 hl1 hl2); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedLayout.values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 2) (by simp [_root_.ThreeSum.ReportingHostWantedLayout.values]) 0
  have hl3 : μ (((layoutHeader : ℤ)+3).toNat)=(L.childR : ℤ) := by
    rw [show ((layoutHeader : ℤ)+3).toNat=layoutHeader+3 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hl0 hl1 hl2 hl3); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedLayout.values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 3) (by simp [_root_.ThreeSum.ReportingHostWantedLayout.values]) 0
  have hl4 : μ (((layoutHeader : ℤ)+4).toNat)=(L.counts : ℤ) := by
    rw [show ((layoutHeader : ℤ)+4).toNat=layoutHeader+4 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hl0 hl1 hl2 hl3 hl4); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedLayout.values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 4) (by simp [_root_.ThreeSum.ReportingHostWantedLayout.values]) 0
  have hl5 : μ (((layoutHeader : ℤ)+5).toNat)=(L.selected : ℤ) := by
    rw [show ((layoutHeader : ℤ)+5).toNat=layoutHeader+5 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hl0 hl1 hl2 hl3 hl4 hl5); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedLayout.values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 5) (by simp [_root_.ThreeSum.ReportingHostWantedLayout.values]) 0
  have hl6 : μ (((layoutHeader : ℤ)+6).toNat)=(L.maskBase : ℤ) := by
    rw [show ((layoutHeader : ℤ)+6).toNat=layoutHeader+6 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hl0 hl1 hl2 hl3 hl4 hl5 hl6); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedLayout.values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 6) (by simp [_root_.ThreeSum.ReportingHostWantedLayout.values]) 0
  have hl7 : μ (((layoutHeader : ℤ)+7).toNat)=(L.terminalMasks : ℤ) := by
    rw [show ((layoutHeader : ℤ)+7).toNat=layoutHeader+7 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedLayout.values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 7) (by simp [_root_.ThreeSum.ReportingHostWantedLayout.values]) 0
  have hl8 : μ (((layoutHeader : ℤ)+8).toNat)=(L.masksL : ℤ) := by
    rw [show ((layoutHeader : ℤ)+8).toNat=layoutHeader+8 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedLayout.values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 8) (by simp [_root_.ThreeSum.ReportingHostWantedLayout.values]) 0
  have hl9 : μ (((layoutHeader : ℤ)+9).toNat)=(L.masksR : ℤ) := by
    rw [show ((layoutHeader : ℤ)+9).toNat=layoutHeader+9 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedLayout.values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 9) (by simp [_root_.ThreeSum.ReportingHostWantedLayout.values]) 0
  have hl10 : μ (((layoutHeader : ℤ)+10).toNat)=(L.base : ℤ) := by
    rw [show ((layoutHeader : ℤ)+10).toNat=layoutHeader+10 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedLayout.values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 10) (by simp [_root_.ThreeSum.ReportingHostWantedLayout.values]) 0
  have hl11 : μ (((layoutHeader : ℤ)+11).toNat)=(L.bitBase : ℤ) := by
    rw [show ((layoutHeader : ℤ)+11).toNat=layoutHeader+11 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedLayout.values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 11) (by simp [_root_.ThreeSum.ReportingHostWantedLayout.values]) 0
  have hl12 : μ (((layoutHeader : ℤ)+12).toNat)=(L.rowOut : ℤ) := by
    rw [show ((layoutHeader : ℤ)+12).toNat=layoutHeader+12 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedLayout.values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 12) (by simp [_root_.ThreeSum.ReportingHostWantedLayout.values]) 0
  have hl13 : μ (((layoutHeader : ℤ)+13).toNat)=(L.work : ℤ) := by
    rw [show ((layoutHeader : ℤ)+13).toNat=layoutHeader+13 by ((try clear! H HL hreport hselected hlayout hprime hcap hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13); omega)]
    simpa only [_root_.ThreeSum.ReportingHostWantedLayout.values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 13) (by simp [_root_.ThreeSum.ReportingHostWantedLayout.values]) 0
  have hv0 : |S.av|≤lim.word := hselected _ (by simp [_root_.ThreeSum.ReportingHostWantedControls.record])
  have hv1 : (S.owner : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.owner : ℤ) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record])
  have hv2 : (S.bandB : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.bandB : ℤ) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record])
  have hv3 : (S.bandC : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.bandC : ℤ) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record])
  have hv4 : (S.catalog : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.catalog : ℤ) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record])
  have hv5 : (S.srcL : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.srcL : ℤ) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record])
  have hv6 : (S.srcR : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.srcR : ℤ) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record])
  have hv7 : (S.offsetsL : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.offsetsL : ℤ) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record])
  have hv8 : (S.flatL : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.flatL : ℤ) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record])
  have hv9 : (S.offsetsR : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.offsetsR : ℤ) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record])
  have hv10 : (S.flatR : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.flatR : ℤ) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record])
  have hv11 : (S.NL : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.NL : ℤ) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record])
  have hv12 : (S.NR : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.NR : ℤ) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record])
  have hv13 : (S.baseL : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.baseL : ℤ) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record])
  have hv14 : (S.baseR : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.baseR : ℤ) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record])
  have hv15 : (S.occ : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.occ : ℤ) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record])
  have hv16 : (S.maps : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.maps : ℤ) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record])
  have hv17 : (S.candidates : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.candidates : ℤ) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record])
  have hv18 : (S.histL : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.histL : ℤ) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record])
  have hv19 : (S.histR : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.histR : ℤ) (by simp [_root_.ThreeSum.ReportingHostWantedControls.record])
  have hw0 : L.root≤lim.space := hlayout _ (by simp [_root_.ThreeSum.ReportingHostWantedLayout.values])
  have hw1 : L.masks≤lim.space := hlayout _ (by simp [_root_.ThreeSum.ReportingHostWantedLayout.values])
  have hw2 : L.childL≤lim.space := hlayout _ (by simp [_root_.ThreeSum.ReportingHostWantedLayout.values])
  have hw3 : L.childR≤lim.space := hlayout _ (by simp [_root_.ThreeSum.ReportingHostWantedLayout.values])
  have hw4 : L.counts≤lim.space := hlayout _ (by simp [_root_.ThreeSum.ReportingHostWantedLayout.values])
  have hw5 : L.selected≤lim.space := hlayout _ (by simp [_root_.ThreeSum.ReportingHostWantedLayout.values])
  have hw6 : L.maskBase≤lim.space := hlayout _ (by simp [_root_.ThreeSum.ReportingHostWantedLayout.values])
  have hw7 : L.terminalMasks≤lim.space := hlayout _ (by simp [_root_.ThreeSum.ReportingHostWantedLayout.values])
  have hw8 : L.masksL≤lim.space := hlayout _ (by simp [_root_.ThreeSum.ReportingHostWantedLayout.values])
  have hw9 : L.masksR≤lim.space := hlayout _ (by simp [_root_.ThreeSum.ReportingHostWantedLayout.values])
  have hw10 : L.base≤lim.space := hlayout _ (by simp [_root_.ThreeSum.ReportingHostWantedLayout.values])
  have hw11 : L.bitBase≤lim.space := hlayout _ (by simp [_root_.ThreeSum.ReportingHostWantedLayout.values])
  have hw12 : L.rowOut≤lim.space := hlayout _ (by simp [_root_.ThreeSum.ReportingHostWantedLayout.values])
  have hw13 : L.work≤lim.space := hlayout _ (by simp [_root_.ThreeSum.ReportingHostWantedLayout.values])
  have hs' := hs
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordCall.space _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordCall.numericExtra at hs'
  have hprimeZ : μ (((cover : ℤ)+6).toNat)=(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ) := by
    rw [show ((cover : ℤ)+6).toNat=cover+6 by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13); omega)]; exact hprime
  have hcapZ : μ (((cover : ℤ)+7).toNat)=(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h : ℤ) := by
    rw [show ((cover : ℤ)+7).toNat=cover+7 by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13); omega)]; exact hcap
  have hcutZ : (J : ℤ)*(2*(h : ℤ))=(_root_.ThreeSum.LightBlockQuery.sourceCut h J : ℤ) := by simp [_root_.ThreeSum.LightBlockQuery.sourceCut]; ring
  have hcutNonneg : (0 : ℤ)≤(J : ℤ)*(2*(h : ℤ)) := by positivity
  have hcutWord : (J : ℤ)*(2*(h : ℤ))≤lim.word := by
    rw [hcutZ]
    exact (Int.ofNat_le.mpr (by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13); omega) : sourceCut h J≤lim.space)).trans hw
  have hcutNonneg' : (0 : ℤ)≤2*(h : ℤ)*(J : ℤ) := by positivity
  have hcutWord' : 2*(h : ℤ)*(J : ℤ)≤lim.word := by
    nlinarith only [hcutWord]
  have hrawZ : (layoutHeader : ℤ)+18+(J : ℤ)=(_root_.ThreeSum.ReportingHostWantedControls.rawRows layoutHeader J : ℤ) := by
    simp [_root_.ThreeSum.ReportingHostWantedControls.rawRows,_root_.ThreeSum.ReportingHostWantedLayout.decoded]; ring
  have hpackedZ : (layoutHeader : ℤ)+38+2*(J : ℤ)=(_root_.ThreeSum.ReportingHostWantedLayout.packed layoutHeader J : ℤ) := by
    simp [_root_.ThreeSum.ReportingHostWantedLayout.packed,_root_.ThreeSum.ReportingHostWantedLayout.access,_root_.ThreeSum.ReportingHostWantedLayout.decoded]; ring
  have hs0Nat : μ selectionHeader=S.av := by simpa only [add_zero,Int.toNat_natCast] using hs0
  have hl0Nat : μ layoutHeader=(L.root : ℤ) := by simpa only [add_zero,Int.toNat_natCast] using hl0
  have hs1Nat : μ (selectionHeader+1)=(S.owner : ℤ) := by
    rw [show selectionHeader+1=((selectionHeader : ℤ)+1).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hl0 hl0Nat hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13); omega)]; exact hs1
  have hs2Nat : μ (selectionHeader+2)=(S.bandB : ℤ) := by
    rw [show selectionHeader+2=((selectionHeader : ℤ)+2).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hl0 hl0Nat hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13); omega)]; exact hs2
  have hs3Nat : μ (selectionHeader+3)=(S.bandC : ℤ) := by
    rw [show selectionHeader+3=((selectionHeader : ℤ)+3).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hl0 hl0Nat hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13); omega)]; exact hs3
  have hs4Nat : μ (selectionHeader+4)=(S.catalog : ℤ) := by
    rw [show selectionHeader+4=((selectionHeader : ℤ)+4).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hl0 hl0Nat hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13); omega)]; exact hs4
  have hs5Nat : μ (selectionHeader+5)=(S.srcL : ℤ) := by
    rw [show selectionHeader+5=((selectionHeader : ℤ)+5).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hl0 hl0Nat hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13); omega)]; exact hs5
  have hs6Nat : μ (selectionHeader+6)=(S.srcR : ℤ) := by
    rw [show selectionHeader+6=((selectionHeader : ℤ)+6).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hl0 hl0Nat hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13); omega)]; exact hs6
  have hs7Nat : μ (selectionHeader+7)=(S.offsetsL : ℤ) := by
    rw [show selectionHeader+7=((selectionHeader : ℤ)+7).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hl0 hl0Nat hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13); omega)]; exact hs7
  have hs8Nat : μ (selectionHeader+8)=(S.flatL : ℤ) := by
    rw [show selectionHeader+8=((selectionHeader : ℤ)+8).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hl0 hl0Nat hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13); omega)]; exact hs8
  have hs9Nat : μ (selectionHeader+9)=(S.offsetsR : ℤ) := by
    rw [show selectionHeader+9=((selectionHeader : ℤ)+9).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hl0 hl0Nat hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13); omega)]; exact hs9
  have hs10Nat : μ (selectionHeader+10)=(S.flatR : ℤ) := by
    rw [show selectionHeader+10=((selectionHeader : ℤ)+10).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hl0 hl0Nat hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13); omega)]; exact hs10
  have hs11Nat : μ (selectionHeader+11)=(S.NL : ℤ) := by
    rw [show selectionHeader+11=((selectionHeader : ℤ)+11).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs13 hs14 hs15 hs16 hs17 hs18 hs19 hl0 hl0Nat hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13); omega)]; exact hs11
  have hs12Nat : μ (selectionHeader+12)=(S.NR : ℤ) := by
    rw [show selectionHeader+12=((selectionHeader : ℤ)+12).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs14 hs15 hs16 hs17 hs18 hs19 hl0 hl0Nat hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13); omega)]; exact hs12
  have hs13Nat : μ (selectionHeader+13)=(S.baseL : ℤ) := by
    rw [show selectionHeader+13=((selectionHeader : ℤ)+13).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs15 hs16 hs17 hs18 hs19 hl0 hl0Nat hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13); omega)]; exact hs13
  have hs14Nat : μ (selectionHeader+14)=(S.baseR : ℤ) := by
    rw [show selectionHeader+14=((selectionHeader : ℤ)+14).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs16 hs17 hs18 hs19 hl0 hl0Nat hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13); omega)]; exact hs14
  have hs15Nat : μ (selectionHeader+15)=(S.occ : ℤ) := by
    rw [show selectionHeader+15=((selectionHeader : ℤ)+15).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs17 hs18 hs19 hl0 hl0Nat hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13); omega)]; exact hs15
  have hs16Nat : μ (selectionHeader+16)=(S.maps : ℤ) := by
    rw [show selectionHeader+16=((selectionHeader : ℤ)+16).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs18 hs19 hl0 hl0Nat hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13); omega)]; exact hs16
  have hs17Nat : μ (selectionHeader+17)=(S.candidates : ℤ) := by
    rw [show selectionHeader+17=((selectionHeader : ℤ)+17).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs19 hl0 hl0Nat hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13); omega)]; exact hs17
  have hs18Nat : μ (selectionHeader+18)=(S.histL : ℤ) := by
    rw [show selectionHeader+18=((selectionHeader : ℤ)+18).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hl0 hl0Nat hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13); omega)]; exact hs18
  have hs19Nat : μ (selectionHeader+19)=(S.histR : ℤ) := by
    rw [show selectionHeader+19=((selectionHeader : ℤ)+19).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13); omega)]; exact hs19
  have hl1Nat : μ (layoutHeader+1)=(L.masks : ℤ) := by
    rw [show layoutHeader+1=((layoutHeader : ℤ)+1).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13); omega)]; exact hl1
  have hl2Nat : μ (layoutHeader+2)=(L.childL : ℤ) := by
    rw [show layoutHeader+2=((layoutHeader : ℤ)+2).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13); omega)]; exact hl2
  have hl3Nat : μ (layoutHeader+3)=(L.childR : ℤ) := by
    rw [show layoutHeader+3=((layoutHeader : ℤ)+3).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13); omega)]; exact hl3
  have hl4Nat : μ (layoutHeader+4)=(L.counts : ℤ) := by
    rw [show layoutHeader+4=((layoutHeader : ℤ)+4).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13); omega)]; exact hl4
  have hl5Nat : μ (layoutHeader+5)=(L.selected : ℤ) := by
    rw [show layoutHeader+5=((layoutHeader : ℤ)+5).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13); omega)]; exact hl5
  have hl6Nat : μ (layoutHeader+6)=(L.maskBase : ℤ) := by
    rw [show layoutHeader+6=((layoutHeader : ℤ)+6).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl8 hl9 hl10 hl11 hl12 hl13); omega)]; exact hl6
  have hl7Nat : μ (layoutHeader+7)=(L.terminalMasks : ℤ) := by
    rw [show layoutHeader+7=((layoutHeader : ℤ)+7).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl9 hl10 hl11 hl12 hl13); omega)]; exact hl7
  have hl8Nat : μ (layoutHeader+8)=(L.masksL : ℤ) := by
    rw [show layoutHeader+8=((layoutHeader : ℤ)+8).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl10 hl11 hl12 hl13); omega)]; exact hl8
  have hl9Nat : μ (layoutHeader+9)=(L.masksR : ℤ) := by
    rw [show layoutHeader+9=((layoutHeader : ℤ)+9).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl11 hl12 hl13); omega)]; exact hl9
  have hl10Nat : μ (layoutHeader+10)=(L.base : ℤ) := by
    rw [show layoutHeader+10=((layoutHeader : ℤ)+10).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl12 hl13); omega)]; exact hl10
  have hl11Nat : μ (layoutHeader+11)=(L.bitBase : ℤ) := by
    rw [show layoutHeader+11=((layoutHeader : ℤ)+11).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl13); omega)]; exact hl11
  have hl12Nat : μ (layoutHeader+12)=(L.rowOut : ℤ) := by
    rw [show layoutHeader+12=((layoutHeader : ℤ)+12).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13); omega)]; exact hl12
  have hl13Nat : μ (layoutHeader+13)=(L.work : ℤ) := by
    rw [show layoutHeader+13=((layoutHeader : ℤ)+13).toNat by ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)]; exact hl13
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 138) (by rfl : program[138]?=some (body 137))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordCall.body
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (S.av : ℤ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hs0Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hs0Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hs0Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (S.owner : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hs1, hs1Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hs1, hs1Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hs1, hs1Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (S.bandB : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hs2, hs2Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hs2, hs2Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hs2, hs2Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (S.bandC : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hs3, hs3Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hs3, hs3Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hs3, hs3Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (S.catalog : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hs4, hs4Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hs4, hs4Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hs4, hs4Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (S.srcL : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hs5, hs5Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hs5, hs5Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hs5, hs5Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (S.srcR : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hs6, hs6Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hs6, hs6Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hs6, hs6Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (S.offsetsL : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hs7, hs7Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hs7, hs7Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hs7, hs7Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (S.flatL : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hs8, hs8Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hs8, hs8Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hs8, hs8Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (S.offsetsR : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hs9, hs9Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hs9, hs9Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hs9, hs9Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (S.flatR : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hs10, hs10Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hs10, hs10Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hs10, hs10Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (S.NL : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hs11, hs11Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hs11, hs11Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hs11, hs11Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (S.NR : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hs12, hs12Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hs12, hs12Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hs12, hs12Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (S.baseL : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hs13, hs13Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hs13, hs13Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hs13, hs13Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (S.baseR : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hs14, hs14Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hs14, hs14Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hs14, hs14Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (S.occ : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hs15, hs15Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hs15, hs15Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hs15, hs15Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (S.maps : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hs16, hs16Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hs16, hs16Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hs16, hs16Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (S.candidates : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hs17, hs17Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hs17, hs17Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hs17, hs17Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (S.histL : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hs18, hs18Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hs18, hs18Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hs18, hs18Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (S.histR : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hs19, hs19Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hs19, hs19Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hs19, hs19Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (L.root : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hl0Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hl0Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hl0Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (L.masks : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hl1, hl1Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hl1, hl1Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hl1, hl1Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (L.childL : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hl2, hl2Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hl2, hl2Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hl2, hl2Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (L.childR : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hl3, hl3Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hl3, hl3Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hl3, hl3Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (L.counts : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hl4, hl4Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hl4, hl4Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hl4, hl4Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (L.selected : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hl5, hl5Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hl5, hl5Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hl5, hl5Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (L.maskBase : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hl6, hl6Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hl6, hl6Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hl6, hl6Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (L.terminalMasks : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hl7, hl7Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hl7, hl7Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hl7, hl7Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (L.masksL : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hl8, hl8Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hl8, hl8Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hl8, hl8Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (L.masksR : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hl9, hl9Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hl9, hl9Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hl9, hl9Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (L.base : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hl10, hl10Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hl10, hl10Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hl10, hl10Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (L.bitBase : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hl11, hl11Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hl11, hl11Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hl11, hl11Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (L.rowOut : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hl12, hl12Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hl12, hl12Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hl12, hl12Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (L.work : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hl13, hl13Nat]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hl13, hl13Nat] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hl13, hl13Nat] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hprimeZ]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hprimeZ] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hprimeZ] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcapZ]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hcapZ] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcapZ] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (464 * h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightBlockQuery.sourceCut h J : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcutZ]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hcutZ] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcutZ] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.ReportingHostWantedControls.rawRows layoutHeader J : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrawZ, _root_.ThreeSum.ReportingHostWantedControls.rawRows, _root_.ThreeSum.ReportingHostWantedLayout.decoded]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hrawZ, _root_.ThreeSum.ReportingHostWantedControls.rawRows, _root_.ThreeSum.ReportingHostWantedLayout.decoded] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrawZ, _root_.ThreeSum.ReportingHostWantedControls.rawRows, _root_.ThreeSum.ReportingHostWantedLayout.decoded] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.ReportingHostWantedLayout.packed layoutHeader J : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hpackedZ, _root_.ThreeSum.ReportingHostWantedLayout.packed, _root_.ThreeSum.ReportingHostWantedLayout.access, _root_.ThreeSum.ReportingHostWantedLayout.decoded]
           first
           | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [hpackedZ, _root_.ThreeSum.ReportingHostWantedLayout.packed, _root_.ThreeSum.ReportingHostWantedLayout.access, _root_.ThreeSum.ReportingHostWantedLayout.decoded] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hpackedZ, _root_.ThreeSum.ReportingHostWantedLayout.packed, _root_.ThreeSum.ReportingHostWantedLayout.access, _root_.ThreeSum.ReportingHostWantedLayout.decoded] <;> ((try clear! H HL hreport hselected hlayout hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hreportRun := hreport.append [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordCall.body 137]
  change _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordCall.program 137 (d+1) _ μ T Q at hreportRun
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hreportRun _ (by ((try clear! H HL hreport hselected hlayout hreportRun hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hreportRun ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls.arguments]
           first
           | ((try clear! H HL hreport hselected hlayout hreportRun hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
           | (ring_nf; ((try clear! H HL hreport hselected hlayout hreportRun hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
       | ((try clear! H HL hreport hselected hlayout hreportRun hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls.arguments] <;>
             first
             | ((try clear! H HL hreport hselected hlayout hreportRun hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
             | (ring_nf; ((try clear! H HL hreport hselected hlayout hreportRun hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)))
     on_goal -1 => ((try clear! H HL hreport hselected hlayout hreportRun hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega)
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls.arguments] <;> ((try clear! H HL hreport hselected hlayout hreportRun hprime hcap hprimeZ hcapZ hs0 hs0Nat hs1 hs1Nat hs2 hs2Nat hs3 hs3Nat hs4 hs4Nat hs5 hs5Nat hs6 hs6Nat hs7 hs7Nat hs8 hs8Nat hs9 hs9Nat hs10 hs10Nat hs11 hs11Nat hs12 hs12Nat hs13 hs13Nat hs14 hs14Nat hs15 hs15Nat hs16 hs16Nat hs17 hs17Nat hs18 hs18Nat hs19 hs19Nat hl0 hl0Nat hl1 hl1Nat hl2 hl2Nat hl3 hl3Nat hl4 hl4Nat hl5 hl5Nat hl6 hl6Nat hl7 hl7Nat hl8 hl8Nat hl9 hl9Nat hl10 hl10Nat hl11 hl11Nat hl12 hl12Nat hl13 hl13Nat); omega))
     on_goal -1 => (rintro result ν hpost; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  exact hpost
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordCall.program_meets__implementation_2a8fd7c113) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordCall.program_meets__implementation_2a8fd7c113)

#print axioms solution
