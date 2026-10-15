-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrime.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:51:52.151464+00:00
-- url     : https://prove2.me/submissions/c54ba7f9-524b-403b-9a8c-68e84d204d75

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightEncodedColorPrimeCore_program_meets
import Theorems.Thm_ThreeSum_BandCandidateRows_fromOwner_sound
import Theorems.Thm_ThreeSum_BandCandidateRows_mem_records_owner

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
namespace ThreeSum.BandPrimeChoice
end ThreeSum.BandPrimeChoice
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BandWeightedScore
end ThreeSum.BandWeightedScore
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.LightBandPrimeStage
end ThreeSum.LightBandPrimeStage
namespace ThreeSum.LightEncodedColorPrime
end ThreeSum.LightEncodedColorPrime
namespace ThreeSum.LightPrimeMinimum
end ThreeSum.LightPrimeMinimum
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SourceFiniteInputs
end ThreeSum.SourceFiniteInputs
namespace ThreeSum.WeightedScore
end ThreeSum.WeightedScore
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
namespace ThreeSum1960614.Machine.ThreeSum.BandPrimeChoice
end ThreeSum1960614.Machine.ThreeSum.BandPrimeChoice
namespace ThreeSum1960614.Machine.ThreeSum.BandRawA
end ThreeSum1960614.Machine.ThreeSum.BandRawA
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.BandWeightedScore
end ThreeSum1960614.Machine.ThreeSum.BandWeightedScore
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBandPrimeStage
end ThreeSum1960614.Machine.ThreeSum.LightBandPrimeStage
namespace ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrime
end ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrime
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
namespace ThreeSum1960614.Machine.ThreeSum.LightPrimeMinimum
end ThreeSum1960614.Machine.ThreeSum.LightPrimeMinimum
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs
end ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs
namespace ThreeSum1960614.Machine.ThreeSum.WeightedScore
end ThreeSum1960614.Machine.ThreeSum.WeightedScore
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











theorem make_flag (mode : _root_.ThreeSum.BandCandidateRows.Mode) (i j r : ℕ) :
    (_root_.ThreeSum.BandCandidateRows.make mode i j r).flag=0 ∨ (_root_.ThreeSum.BandCandidateRows.make mode i j r).flag=1 := by
  cases mode <;> simp only [_root_.ThreeSum.BandCandidateRows.make] <;> split_ifs <;> simp













end ThreeSum.BandCandidateRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Executing deterministic prime-score minimization

The same finite prime array supplies the candidate multipliers and the
auxiliary tests. The program streams exact scores at `q * primes i`, retaining
the first minimum. All weighted-score calls reuse one scratch region.
-/

namespace ThreeSum.LightPrimeMinimum
open _root_.ThreeSum.LightPrimeMinimum


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.WeightedScore
open _root_.ThreeSum1960614.Machine.ThreeSum.WeightedScore

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000











theorem score_congr {primes : ℕ → ℕ} {s q nA nB nC : ℕ} {A A' B B' C C' : ℕ → ℤ}
    (ha : ∀ i < nA, A i = A' i) (hb : ∀ i < nB, B i = B' i)
    (hc : ∀ i < nC, C i = C' i) :
    _root_.ThreeSum.WeightedScore.score primes s q nA nB nC A B C = _root_.ThreeSum.WeightedScore.score primes s q nA nB nC A' B' C' := by
  unfold _root_.ThreeSum.WeightedScore.score _root_.ThreeSum.Arithmetic.weightedFalseCount
  apply Finset.sum_congr rfl
  intro t ht
  simp only [_root_.ThreeSum.ModuloCounts.triples, Finset.mem_product, Finset.mem_range] at ht
  simp only [_root_.ThreeSum.ModuloCounts.difference, ha _ ht.1, hb _ ht.2.1, hc _ ht.2.2]
  rfl











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}













end ThreeSum.LightPrimeMinimum

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # List and memory interfaces for the exact candidate record array -/

namespace ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandCandidateRows


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration

set_option maxHeartbeats 1300000



theorem records_sound {A B C : _root_.ThreeSum.BandEnumeration.Family} {r : _root_.ThreeSum.BandCandidateRows.Record}
    (hr : r ∈ _root_.ThreeSum.BandCandidateRows.records A B C) (hf : r.flag=1) :
    r.a < A.size ∧ r.b < B.size ∧ r.c < C.size ∧
      _root_.ThreeSum.Bands.Relevant A.lower A.upper B.lower B.upper C.lower C.upper (r.a,r.b,r.c) := by
  obtain ⟨o,rfl⟩ := _root_.ThreeSum.BandCandidateRows.mem_records_owner hr
  exact _root_.ThreeSum.BandCandidateRows.fromOwner_sound A B C o hf

theorem records_flag {A B C : _root_.ThreeSum.BandEnumeration.Family} {r : _root_.ThreeSum.BandCandidateRows.Record} (hr : r ∈ _root_.ThreeSum.BandCandidateRows.records A B C) :
    r.flag=0 ∨ r.flag=1 := by
  obtain ⟨o,rfl⟩ := _root_.ThreeSum.BandCandidateRows.mem_records_owner hr
  rcases o with ⟨j,k⟩ | ⟨i,j | k⟩ <;> exact _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.make_flag _ _ _ _











end ThreeSum.BandCandidateRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The aggregate weighted score of physical band-owner candidates

Each flagged owner contributes the score of its three actual truncated
bands. Owner multiplicities are retained. The contraction and initial bound
therefore apply to the same quadratic catalog that the program scans.
-/

namespace ThreeSum.BandWeightedScore
open _root_.ThreeSum.BandWeightedScore


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.Finset
open scoped _root_.BigOperators

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000







theorem position_lt {n g a i : ℕ} (hi : i < _root_.ThreeSum.BandWeightedScore.length n g a) : a*g+i < n := by
  have hh := min_le_right g (n-a*g)
  unfold _root_.ThreeSum.BandWeightedScore.length at hi
  omega



















theorem block_congr {primes : ℕ → ℕ} {s q nA nB nC g : ℕ}
    {A A' B B' C C' : ℕ → ℤ} (r : _root_.ThreeSum.BandCandidateRows.Record)
    (hA : ∀ i < nA, A i=A' i) (hB : ∀ i < nB, B i=B' i) (hC : ∀ i < nC, C i=C' i) :
    _root_.ThreeSum.BandWeightedScore.block primes s q nA nB nC g A B C r=_root_.ThreeSum.BandWeightedScore.block primes s q nA nB nC g A' B' C' r := by
  unfold _root_.ThreeSum.BandWeightedScore.block
  split_ifs
  · exact _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimeMinimum.score_congr
      (fun i hi => hA _ (_root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.position_lt hi)) (fun i hi => hB _ (_root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.position_lt hi))
      (fun i hi => hC _ (_root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.position_lt hi))
  · rfl

theorem score_congr {primes : ℕ → ℕ} {s q nA nB nC g : ℕ}
    {A A' B B' C C' : ℕ → ℤ} (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (hA : ∀ i < nA, A i=A' i) (hB : ∀ i < nB, B i=B' i) (hC : ∀ i < nC, C i=C' i) :
    _root_.ThreeSum.BandWeightedScore.score primes s q nA nB nC g A B C rs=_root_.ThreeSum.BandWeightedScore.score primes s q nA nB nC g A' B' C' rs := by
  unfold _root_.ThreeSum.BandWeightedScore.score _root_.ThreeSum.BandWeightedScore.partialScore
  exact sum_congr rfl fun i _ => _root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.block_congr (rs.getD i default) hA hB hC





end ThreeSum.BandWeightedScore

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A common contracting modulus for the complete band-owner catalog

The same deterministic first-minimum rule is applied to the sum of every
flagged owner's score. These are joint choices for all bands, rather than
independent moduli whose contractions could not be combined.
-/

namespace ThreeSum.BandPrimeChoice
open _root_.ThreeSum.BandPrimeChoice


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandWeightedScore
open _root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore
open _root_.Finset
open scoped _root_.BigOperators

set_option maxHeartbeats 1400000
set_option maxRecDepth 8000























theorem chosenPrime_congr {primes : ℕ → ℕ} {s q nA nB nC g : ℕ}
    {A A' B B' C C' : ℕ → ℤ} (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (hA : ∀ i < nA, A i=A' i) (hB : ∀ i < nB, B i=B' i) (hC : ∀ i < nC, C i=C' i) :
    _root_.ThreeSum.BandPrimeChoice.chosenPrime primes s q nA nB nC g A B C rs=_root_.ThreeSum.BandPrimeChoice.chosenPrime primes s q nA nB nC g A' B' C' rs := by
  have hf : _root_.ThreeSum.BandPrimeChoice.candidateScore primes s q nA nB nC g A B C rs=
      _root_.ThreeSum.BandPrimeChoice.candidateScore primes s q nA nB nC g A' B' C' rs := by
    funext i
    unfold _root_.ThreeSum.BandPrimeChoice.candidateScore
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.score_congr rs hA hB hC]
  simp only [_root_.ThreeSum.BandPrimeChoice.chosenPrime,_root_.ThreeSum.BandPrimeChoice.chosenIndex,hf]

theorem modulus_congr {primes : ℕ → ℕ} {s nA nB nC g : ℕ}
    {A A' B B' C C' : ℕ → ℤ} (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (hA : ∀ i < nA, A i=A' i) (hB : ∀ i < nB, B i=B' i) (hC : ∀ i < nC, C i=C' i) (r : ℕ) :
    _root_.ThreeSum.BandPrimeChoice.modulus primes s nA nB nC g A B C rs r=_root_.ThreeSum.BandPrimeChoice.modulus primes s nA nB nC g A' B' C' rs r := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [_root_.ThreeSum.BandPrimeChoice.modulus,ih,_root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeChoice.chosenPrime_congr rs hA hB hC]

end ThreeSum.BandPrimeChoice

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










theorem prepared_read {μ : ℕ → ℤ} {values endpoints g : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Represents μ values endpoints g hg original L hs) :
    ∀ j < L.length, μ (values+j)=L.getD j 0 := fun j hj => H.1.getD hj 0

theorem prepared_headers {μ : ℕ → ℤ} {values endpoints g : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Represents μ values endpoints g hg original L hs) :
    μ endpoints=(L.length : ℤ) ∧ μ (endpoints+1)=(_root_.ThreeSum.BandPartition.size L.length g : ℤ) :=
  ⟨H.2.2.2.1,H.2.2.2.2.1⟩

theorem prepared_bound {μ : ℕ → ℤ} {values endpoints g U : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Represents μ values endpoints g hg original L hs)
    (hb : ∀ z ∈ original, |z| ≤ (U : ℤ)) :
    ∀ j < L.length, |L.getD j 0| ≤ (U : ℤ) := by
  intro j hj
  rw [List.getD_eq_getElem _ _ hj]
  exact hb _ ((H.2.2.1 _).mp (List.getElem_mem hj))







end ThreeSum.SourceFiniteInputs

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The executed common-prime stage at the actual integer schedule

This interface consumes the physical records produced by the band catalog.
It derives every flag, band-start and candidate-count premise from that
catalog, computes the depth and pool, and returns the arithmetic guard and
the finite physical-domain false-mass bound at the actual execution cost.
-/

namespace ThreeSum.LightBandPrimeStage
open _root_.ThreeSum.LightBandPrimeStage


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000





theorem records_valid {A B C : _root_.ThreeSum.BandEnumeration.Family} {nA nB nC g : ℕ}
    (hA : A.size=_root_.ThreeSum.BandPartition.size nA g)
    (hB : B.size=_root_.ThreeSum.BandPartition.size nB g)
    (hC : C.size=_root_.ThreeSum.BandPartition.size nC g) (hg : 0 < g) :
    ∀ r ∈ _root_.ThreeSum.BandCandidateRows.records A B C, r.flag=1 → r.a*g ≤ nA ∧ r.b*g ≤ nB ∧ r.c*g ≤ nC := by
  intro r hr hf
  obtain ⟨ha,hb,hc,_⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.records_sound hr hf
  rw [hA] at ha
  rw [hB] at hb
  rw [hC] at hc
  exact ⟨(_root_.ThreeSum.BandPartition.start_lt hg ha).le,(_root_.ThreeSum.BandPartition.start_lt hg hb).le,
    (_root_.ThreeSum.BandPartition.start_lt hg hc).le⟩





variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c n nA nB nC k recs free : ℕ}



end ThreeSum.LightBandPrimeStage

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightEncodedColorPrime
open _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrime

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ} {μ : ℕ → ℤ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrime.program_meets__implementation_336012000a {av ae bv be cv ce tables rec vals g M y free maxMod U : ℕ} {hg : 0 < g}
    {originalA originalB originalC A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)} {rA : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hy : 0 < y)
    (hav : av+A.length ≤ free) (hbv : bv+B.length ≤ free) (hcv : cv+C.length ≤ free)
    (hae : ae+2 ≤ free) (hbe : be+2 ≤ free) (hce : ce+2 ≤ free)
    (hrec : rec+4*_root_.ThreeSum.LightEncodedColorPrime.count A.length B.length C.length g ≤ free)
    (hspace : _root_.ThreeSum.LightEncodedColorPrimeCore.space free maxMod g M y U ≤ lim.space)
    (hword : (_root_.ThreeSum.LightEncodedColorPrime.word maxMod A.length B.length C.length g M y U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 maxMod+10 ≤ lim.depth)
    (hA : ∀ z ∈ originalA, |z| ≤ (U : ℤ))
    (hB : ∀ z ∈ originalB, |z| ≤ (U : ℤ))
    (hC : ∀ z ∈ originalC, |z| ≤ (U : ℤ))
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteData.Normalized μ av ae bv be cv ce tables rec vals g hg
      originalA originalB originalC A B C hsA hsB hsC rA)
    (hmax : (4*y)^(_root_.ThreeSum.LightBandPrimeDepth.depth M y+1) ≤ maxMod) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrime.program 24 d [av,ae,bv,be,cv,ce,g,rec,M,y,free] μ
      (_root_.ThreeSum.LightEncodedColorPrime.time maxMod A.length B.length C.length g M y U)
      (fun result ν =>
        result=(_root_.ThreeSum.LightEncodedColorPrime.moduli A B C g hg hsA hsB hsC y (_root_.ThreeSum.LightBandPrimeDepth.depth M y) : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeData.Stored ν free M y (_root_.ThreeSum.LightEncodedColorPrime.moduli A B C g hg hsA hsB hsC y) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν free) := by
  obtain ⟨_,repA,repB,repC,_,recordRows,_⟩ := H
  obtain ⟨hlenA,hcountA⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.prepared_headers repA
  obtain ⟨hlenB,hcountB⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.prepared_headers repB
  obtain ⟨hlenC,hcountC⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.prepared_headers repC
  let rs := _root_.ThreeSum.BandRawA.sortedRecords A B C g hg hsA hsB hsC
  have hrs : rs.length=_root_.ThreeSum.LightEncodedColorPrime.count A.length B.length C.length g := by
    simp only [rs,_root_.ThreeSum.BandRawA.sortedRecords,_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.records_length]
    rfl
  have hsrcA := _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.prepared_read repA
  have hsrcB := _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.prepared_read repB
  have hsrcC := _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.prepared_read repC
  have hbA := _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.prepared_bound repA hA
  have hbB := _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.prepared_bound repB hB
  have hbC := _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.prepared_bound repC hC
  have hcoreWord : (_root_.ThreeSum.LightEncodedColorPrimeCore.word maxMod A.length B.length C.length g
      (_root_.ThreeSum.LightEncodedColorPrime.count A.length B.length C.length g) M y U : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show _root_.ThreeSum.LightEncodedColorPrimeCore.word maxMod A.length B.length C.length g
      (_root_.ThreeSum.LightEncodedColorPrime.count A.length B.length C.length g) M y U ≤ _root_.ThreeSum.LightEncodedColorPrime.word maxMod A.length B.length C.length g M y U by unfold _root_.ThreeSum.LightEncodedColorPrime.word; omega)).trans hword
  have hall (z : ℕ) (hz : z ≤ _root_.ThreeSum.LightEncodedColorPrime.word maxMod A.length B.length C.length g M y U) : (z : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hz).trans hword
  have hnA := hall A.length (by unfold _root_.ThreeSum.LightEncodedColorPrime.word; omega)
  have hnB := hall B.length (by unfold _root_.ThreeSum.LightEncodedColorPrime.word; omega)
  have hnC := hall C.length (by unfold _root_.ThreeSum.LightEncodedColorPrime.word; omega)
  have hGA := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le A.length g
  have hGB := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le B.length g
  have hGC := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le C.length g
  have hcount := hall (_root_.ThreeSum.LightEncodedColorPrime.count A.length B.length C.length g) (by unfold _root_.ThreeSum.LightEncodedColorPrime.word; omega)
  have hcountZ : (_root_.ThreeSum.BandPartition.size B.length g : ℤ)*(_root_.ThreeSum.BandPartition.size C.length g : ℤ)+
      (_root_.ThreeSum.BandPartition.size A.length g : ℤ)*(_root_.ThreeSum.BandPartition.size B.length g : ℤ)+(_root_.ThreeSum.BandPartition.size A.length g : ℤ)*(_root_.ThreeSum.BandPartition.size C.length g : ℤ) ≤ lim.word := by
    simpa only [_root_.ThreeSum.LightEncodedColorPrime.count,Nat.cast_add,Nat.cast_mul] using hcount
  have hBC0 : (0 : ℤ) ≤ (_root_.ThreeSum.BandPartition.size B.length g : ℤ)*(_root_.ThreeSum.BandPartition.size C.length g : ℤ) := by positivity
  have hAB0 : (0 : ℤ) ≤ (_root_.ThreeSum.BandPartition.size A.length g : ℤ)*(_root_.ThreeSum.BandPartition.size B.length g : ℤ) := by positivity
  have hAC0 : (0 : ℤ) ≤ (_root_.ThreeSum.BandPartition.size A.length g : ℤ)*(_root_.ThreeSum.BandPartition.size C.length g : ℤ) := by positivity
  have hfree : free+6 ≤ lim.space := by
    have hh := (le_max_left _ _).trans hspace
    unfold _root_.ThreeSum.LightPrimePool.space _root_.ThreeSum.EncodedColorPrimeData.poolBase at hh
    omega
  have haa : ((ae : ℤ)+1).toNat=ae+1 := by omega
  have hba : ((be : ℤ)+1).toNat=be+1 := by omega
  have hca : ((ce : ℤ)+1).toNat=ce+1 := by omega
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 24) (by rfl : program[24]?=some (body 23))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrime.body _root_.ThreeSum.LightEncodedColorPrime.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (A.length : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hlenA]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hlenA] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hlenA] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (B.length : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hlenB]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hlenB] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hlenB] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (C.length : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hlenC]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hlenC] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hlenC] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.BandPartition.size A.length g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcountA, haa]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hcountA, haa] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcountA, haa] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.BandPartition.size B.length g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcountB, hba]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hcountB, hba] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcountB, hba] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.BandPartition.size C.length g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcountC, hca]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hcountC, hca] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcountC, hca] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightEncodedColorPrime.count A.length B.length C.length g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightEncodedColorPrime.count]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightEncodedColorPrime.count] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightEncodedColorPrime.count] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hflags : ∀ r ∈ rs, r.flag=0 ∨ r.flag=1 := fun _ hr => _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.records_flag hr
  have hvalid : ∀ r ∈ rs, r.flag=1 → r.a*g ≤ A.length ∧ r.b*g ≤ B.length ∧ r.c*g ≤ C.length :=
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeStage.records_valid rfl rfl rfl hg
  have hCore := (_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeCore.program_meets (d := d+1) (μ := μ)
    (a := av) (b := bv) (c := cv) (nA := A.length) (nB := B.length) (nC := C.length)
    (g := g) (recs := rec) (M := M) (y := y) (free := free) (maxMod := maxMod) (U := U)
    rs hw hy hg hav hbv hcv (by simpa only [hrs] using hrec) hspace
    (by simpa only [hrs] using hcoreWord) (by omega) recordRows hflags hvalid
    (fun i hi => by rw [hsrcA i hi]; exact hbA i hi)
    (fun i hi => by rw [hsrcB i hi]; exact hbB i hi)
    (fun i hi => by rw [hsrcC i hi]; exact hbC i hi) hmax).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrime.body 23]
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hCore _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hCore ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrs]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hrs] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrs] <;> omega)
     on_goal -1 => (rintro result ν ⟨hresult, hdata, hkeep⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hmod : _root_.ThreeSum.LightBandPrimeConstruction.modulus y A.length B.length C.length g
      (fun j => μ (av+j)) (fun j => μ (bv+j)) (fun j => μ (cv+j)) rs=
      _root_.ThreeSum.LightEncodedColorPrime.moduli A B C g hg hsA hsB hsC y := by
    funext i
    exact _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeChoice.modulus_congr rs hsrcA hsrcB hsrcC i
  rw [hmod] at hresult hdata
  exact ⟨hresult,hdata,hkeep⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrime.program_meets__implementation_336012000a) := (@ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrime.program_meets__implementation_336012000a)

#print axioms solution
