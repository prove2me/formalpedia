-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeCore.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:47:27.917186+00:00
-- url     : https://prove2.me/submissions/7f266bfa-c96c-4cf1-a894-374682903434

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
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
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
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
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
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
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandPrimeChain_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandPrimeDepth_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightPrimePool_Procs_meets
import Theorems.Thm_ThreeSum_LightPrimePool_prefix_increasing

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
namespace ThreeSum.BandPrimeChoice
end ThreeSum.BandPrimeChoice
namespace ThreeSum.BandWeightedScore
end ThreeSum.BandWeightedScore
namespace ThreeSum.EncodedColorPrimeData
end ThreeSum.EncodedColorPrimeData
namespace ThreeSum.LightBandPrimeConstruction
end ThreeSum.LightBandPrimeConstruction
namespace ThreeSum.LightBandPrimeDepth
end ThreeSum.LightBandPrimeDepth
namespace ThreeSum.LightBandPrimeMinimum
end ThreeSum.LightBandPrimeMinimum
namespace ThreeSum.LightEncodedColorPrimeCore
end ThreeSum.LightEncodedColorPrimeCore
namespace ThreeSum.LightMinimum
end ThreeSum.LightMinimum
namespace ThreeSum.LightPrimeMinimum
end ThreeSum.LightPrimeMinimum
namespace ThreeSum.LightPrimePool
end ThreeSum.LightPrimePool
namespace ThreeSum.ReportingHostRelocation
end ThreeSum.ReportingHostRelocation
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
namespace ThreeSum1960614.Machine.ThreeSum.BandPrimeChoice
end ThreeSum1960614.Machine.ThreeSum.BandPrimeChoice
namespace ThreeSum1960614.Machine.ThreeSum.BandWeightedScore
end ThreeSum1960614.Machine.ThreeSum.BandWeightedScore
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeData
namespace ThreeSum1960614.Machine.ThreeSum.LightBandPrimeConstruction
end ThreeSum1960614.Machine.ThreeSum.LightBandPrimeConstruction
namespace ThreeSum1960614.Machine.ThreeSum.LightBandPrimeDepth
end ThreeSum1960614.Machine.ThreeSum.LightBandPrimeDepth
namespace ThreeSum1960614.Machine.ThreeSum.LightBandPrimeMinimum
end ThreeSum1960614.Machine.ThreeSum.LightBandPrimeMinimum
namespace ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeCore
end ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeCore
namespace ThreeSum1960614.Machine.ThreeSum.LightMinimum
end ThreeSum1960614.Machine.ThreeSum.LightMinimum
namespace ThreeSum1960614.Machine.ThreeSum.LightPrimeMinimum
end ThreeSum1960614.Machine.ThreeSum.LightPrimeMinimum
namespace ThreeSum1960614.Machine.ThreeSum.LightPrimePool
end ThreeSum1960614.Machine.ThreeSum.LightPrimePool
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
end ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
namespace ThreeSum1960614.Machine.ThreeSum.WeightedScore
end ThreeSum1960614.Machine.ThreeSum.WeightedScore
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































theorem cells_length (rs : List _root_.ThreeSum.BandCandidateRows.Record) : (_root_.ThreeSum.BandCandidateRows.cells rs).length=4*rs.length := by
  induction rs with
  | nil => simp [_root_.ThreeSum.BandCandidateRows.cells]
  | cons r rs ih => simp only [_root_.ThreeSum.BandCandidateRows.cells,List.flatMap_cons,List.length_append,_root_.ThreeSum.BandCandidateRows.Record.cells,
      List.length_cons,List.length_nil] at *; omega























end ThreeSum.BandCandidateRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Compute the prescribed common-prime depth without division

The loop compares successive `4*(4*y)^(i+1)` with the radix. It returns
exactly `Nat.log (4*y) (R/4)`, including the zero-depth case. Only local
variables change, and the number of iterations is that logarithm.
-/

namespace ThreeSum.LightBandPrimeDepth
open _root_.ThreeSum.LightBandPrimeDepth


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000








variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ} {R y : ℕ}





theorem program_meets (hy : 0 < y) (hword : (_root_.ThreeSum.LightBandPrimeDepth.word R y : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeDepth.program 0 d [R,y] μ (_root_.ThreeSum.LightBandPrimeDepth.time R y)
      (fun result ν => result=(_root_.ThreeSum.LightBandPrimeDepth.depth R y : ℤ) ∧ ν=μ) := _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeDepth.meets rfl hy hword



end ThreeSum.LightBandPrimeDepth

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A finite array minimum scan in the benchmark language

The selected index is a deterministic left-to-right minimum. Its value
can therefore instantiate the exact mean bound for offset balancing.
-/

namespace ThreeSum.LightMinimum
open _root_.ThreeSum.LightMinimum


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light



theorem least_lt (f : ℕ → ℤ) {n : ℕ} (hn : 0 < n) : _root_.ThreeSum.LightMinimum.least f n < n := by
  induction n with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero => simp [_root_.ThreeSum.LightMinimum.least]
      | succ n =>
          have h := ih (by omega)
          unfold _root_.ThreeSum.LightMinimum.least
          split <;> omega











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



end ThreeSum.LightMinimum

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Executing the candidate prime pool

This fixed program scans the integers in `(y,4*y]`, invokes the concrete
trial-division procedure, and writes every prime exactly once in increasing
order. The returned length and written array are the exact candidate pool
used by the contraction and auxiliary-weight theorems.
-/

namespace ThreeSum.LightPrimePool
open _root_.ThreeSum.LightPrimePool


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000



theorem prefix_length_le (y i : ℕ) : (_root_.ThreeSum.LightPrimePool.scanned y i).length ≤ i := by
  induction i with
  | zero => simp [_root_.ThreeSum.LightPrimePool.scanned]
  | succ i ih =>
      unfold _root_.ThreeSum.LightPrimePool.scanned
      split
      · simp only [List.length_append,List.length_singleton]
        omega
      · omega





theorem prefix_nodup (y i : ℕ) : (_root_.ThreeSum.LightPrimePool.scanned y i).Nodup :=
  (_root_.ThreeSum.LightPrimePool.prefix_increasing y i).imp (fun h => Nat.ne_of_lt h)






theorem values_nodup (y : ℕ) : (_root_.ThreeSum.LightPrimePool.values y).Nodup := _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prefix_nodup y (3*y)
theorem size_le (y : ℕ) : _root_.ThreeSum.LightPrimePool.size y ≤ 3*y := _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prefix_length_le y (3*y)









theorem prime_spec {y i : ℕ} (hi : i < _root_.ThreeSum.LightPrimePool.size y) :
    Nat.Prime (_root_.ThreeSum.LightPrimePool.prime y i) ∧ y < _root_.ThreeSum.LightPrimePool.prime y i ∧ _root_.ThreeSum.LightPrimePool.prime y i ≤ 4*y :=
  _root_.ThreeSum.LightPrimePool.mem_values.mp (_root_.ThreeSum.LightPrimePool.prime_mem hi)

theorem prime_injective {y i j : ℕ} (hi : i < _root_.ThreeSum.LightPrimePool.size y) (hj : j < _root_.ThreeSum.LightPrimePool.size y)
    (heq : _root_.ThreeSum.LightPrimePool.prime y i = _root_.ThreeSum.LightPrimePool.prime y j) : i = j :=
  (List.getD_inj hi hj (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.values_nodup y)).mp heq



theorem values_nonempty {y : ℕ} (hy : 0 < y) : _root_.ThreeSum.LightPrimePool.values y ≠ [] := by
  obtain ⟨p,hp,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul y hy.ne'
  have hmem : p ∈ _root_.ThreeSum.LightPrimePool.values y := _root_.ThreeSum.LightPrimePool.mem_values.mpr ⟨hp,hlo,by omega⟩
  intro heq
  simpa only [heq,List.not_mem_nil] using hmem

theorem size_pos {y : ℕ} (hy : 0 < y) : 0 < _root_.ThreeSum.LightPrimePool.size y :=
  List.length_pos_iff.mpr (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.values_nonempty hy)



















variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem program_meets
    {μ : ℕ → ℤ} {y free : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hy : 0 < y) (hspace : _root_.ThreeSum.LightPrimePool.space free y ≤ lim.space)
    (hword : (_root_.ThreeSum.LightPrimePool.word y : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.program 0 d [y,free] μ (_root_.ThreeSum.LightPrimePool.time y)
      (fun r μ' => r = (_root_.ThreeSum.LightPrimePool.size y : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.SegN μ' free (_root_.ThreeSum.LightPrimePool.values y) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ μ' free) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.program_procs.meets hw hd hy hspace hword

end ThreeSum.LightPrimePool

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







theorem chosenIndex_lt (primes : ℕ → ℕ) {s q nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) (hs : 0 < s) :
    _root_.ThreeSum.BandPrimeChoice.chosenIndex primes s q nA nB nC g A B C rs < s := _root_.ThreeSum1960614.Machine.ThreeSum.LightMinimum.least_lt _ hs







theorem modulus_bounds (primes : ℕ → ℕ) {s nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) (hs : 0 < s) (y Y r : ℕ)
    (hlo : ∀ i < s, y ≤ primes i) (hhi : ∀ i < s, primes i ≤ Y) :
    y^r ≤ _root_.ThreeSum.BandPrimeChoice.modulus primes s nA nB nC g A B C rs r ∧
      _root_.ThreeSum.BandPrimeChoice.modulus primes s nA nB nC g A B C rs r ≤ Y^r := by
  induction r with
  | zero => simp [_root_.ThreeSum.BandPrimeChoice.modulus]
  | succ r ih =>
    have hidx := _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeChoice.chosenIndex_lt (q := _root_.ThreeSum.BandPrimeChoice.modulus primes s nA nB nC g A B C rs r)
      (nA := nA) (nB := nB) (nC := nC) (g := g) primes A B C rs hs
    constructor
    · simpa only [_root_.ThreeSum.BandPrimeChoice.modulus,pow_succ,_root_.ThreeSum.BandPrimeChoice.chosenPrime] using Nat.mul_le_mul ih.1 (hlo _ hidx)
    · simpa only [_root_.ThreeSum.BandPrimeChoice.modulus,pow_succ,_root_.ThreeSum.BandPrimeChoice.chosenPrime] using Nat.mul_le_mul ih.2 (hhi _ hidx)







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

/-!
# Execute common-prime minimization over all owner candidates

Every candidate prime is scored by the actual aggregate band loop. The
first minimum is returned, with no supplied score array or counting oracle.
-/

namespace ThreeSum.LightBandPrimeMinimum
open _root_.ThreeSum.LightBandPrimeMinimum


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandWeightedScore
open _root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore
open _root_.ThreeSum.BandPrimeChoice
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeChoice

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000











theorem maxMod_le_word (maxMod nA nB nC g R s U : ℕ) :
    maxMod ≤ _root_.ThreeSum.LightBandWeightedScore.word maxMod nA nB nC g R s U := by
  unfold _root_.ThreeSum.LightBandWeightedScore.word _root_.ThreeSum.LightBandWeightedScoreCell.word _root_.ThreeSum.LightWeightedScore.word
  omega

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs q aux s free maxMod U : ℕ}



end ThreeSum.LightBandPrimeMinimum

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Construct the prime pool and common contracting modulus from band records

The fixed host constructs the candidate prime array, then executes the
aggregate modulus chain on every owner record. The physical prime array and
every prefix modulus remain available to the encoder and reporting stages.
-/

namespace ThreeSum.LightBandPrimeConstruction
open _root_.ThreeSum.LightBandPrimeConstruction


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000



theorem modulus_bounds {y nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) (levels : ℕ) (hy : 0 < y) :
    y^levels ≤ _root_.ThreeSum.LightBandPrimeConstruction.modulus y nA nB nC g A B C rs levels ∧
      _root_.ThreeSum.LightBandPrimeConstruction.modulus y nA nB nC g A B C rs levels ≤ (4*y)^levels :=
  _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeChoice.modulus_bounds (_root_.ThreeSum.LightPrimePool.prime y) A B C rs
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.size_pos hy) y (4*y) levels
    (fun i hi => (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prime_spec hi).2.1.le)
    (fun i hi => (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prime_spec hi).2.2)















variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs y levels free maxMod U : ℕ}



end ThreeSum.LightBandPrimeConstruction

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightEncodedColorPrimeCore
open _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeCore

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.EncodedColorPrimeData
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeData
set_option maxHeartbeats 2600000
set_option maxRecDepth 13000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs M y free maxMod U : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeCore.program_meets__implementation_60a0d335c2 (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (hw : (lim.space : ℤ) ≤ lim.word) (hy : 0 < y) (hg : 0 < g)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hrecs : recs+4*rs.length ≤ free)
    (hspace : _root_.ThreeSum.LightEncodedColorPrimeCore.space free maxMod g M y U ≤ lim.space)
    (hword : (_root_.ThreeSum.LightEncodedColorPrimeCore.word maxMod nA nB nC g rs.length M y U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 maxMod+9 ≤ lim.depth)
    (hrecords : _root_.ThreeSum1960614.Machine.Light.Seg μ recs (_root_.ThreeSum.BandCandidateRows.cells rs))
    (hflag : ∀ r ∈ rs, r.flag=0 ∨ r.flag=1)
    (hvalid : ∀ r ∈ rs, r.flag=1 → r.a*g ≤ nA ∧ r.b*g ≤ nB ∧ r.c*g ≤ nC)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ))
    (hmax : (4*y)^(_root_.ThreeSum.LightBandPrimeDepth.depth M y+1) ≤ maxMod) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeCore.program 23 d [a,b,c,nA,nB,nC,g,recs,rs.length,M,y,free] μ
      (_root_.ThreeSum.LightEncodedColorPrimeCore.time maxMod g rs.length M y U)
      (fun result ν =>
        result=(_root_.ThreeSum.LightBandPrimeConstruction.modulus y nA nB nC g
          (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) rs (_root_.ThreeSum.LightBandPrimeDepth.depth M y) : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeData.Stored ν free M y
          (_root_.ThreeSum.LightBandPrimeConstruction.modulus y nA nB nC g
            (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) rs) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν free) := by
  let qs := _root_.ThreeSum.LightBandPrimeConstruction.modulus y nA nB nC g
    (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) rs
  have hdWord : (_root_.ThreeSum.LightBandPrimeDepth.word M y : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_left _ _)).trans hword
  have hpWord : (_root_.ThreeSum.LightPrimePool.word y : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ((le_max_left _ _).trans (le_max_right _ _))).trans hword
  have hcWord : (_root_.ThreeSum.LightBandWeightedScore.word maxMod nA nB nC g rs.length (_root_.ThreeSum.LightPrimePool.size y) U : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ((le_max_right _ _).trans (le_max_right _ _))).trans hword
  have hpSpace : _root_.ThreeSum.LightPrimePool.space (_root_.ThreeSum.EncodedColorPrimeData.poolBase free) y ≤ lim.space := (le_max_left _ _).trans hspace
  have hcSpace : _root_.ThreeSum.LightBandPrimeChain.space (_root_.ThreeSum.EncodedColorPrimeData.prefixBase free y) maxMod g U (_root_.ThreeSum.LightBandPrimeDepth.depth M y) ≤ lim.space :=
    (le_max_right _ _).trans hspace
  have hpoolEnd : free+6+3*y ≤ lim.space := by unfold _root_.ThreeSum.LightPrimePool.space _root_.ThreeSum.EncodedColorPrimeData.poolBase at hpSpace; omega
  have hnext : _root_.ThreeSum.EncodedColorPrimeData.nextFree free M y ≤ lim.space := by
    have hh := (le_max_right _ _).trans hcSpace
    change _root_.ThreeSum.EncodedColorPrimeData.prefixBase free y+_root_.ThreeSum.LightBandPrimeDepth.depth M y+1+(Nat.log 2 (maxMod+1)+2) ≤ lim.space at hh
    exact (Nat.le_add_right _ _).trans hh
  have hnext' : free+6+3*y+_root_.ThreeSum.LightBandPrimeDepth.depth M y+1 ≤ lim.space := hnext
  have hnextAddress : _root_.ThreeSum.EncodedColorPrimeData.prefixBase free y+_root_.ThreeSum.LightBandPrimeDepth.depth M y+1 ≤ lim.space := hnext
  have hsize := _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.size_le y
  have hmaxWord : (maxMod : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeMinimum.maxMod_le_word maxMod nA nB nC g rs.length (_root_.ThreeSum.LightPrimePool.size y) U)).trans hcWord
  have hqBound := (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeConstruction.modulus_bounds (nA := nA) (nB := nB) (nC := nC) (g := g)
    (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) rs (_root_.ThreeSum.LightBandPrimeDepth.depth M y) hy).2
  have hqMax : qs (_root_.ThreeSum.LightBandPrimeDepth.depth M y) ≤ maxMod := hqBound.trans
    ((Nat.pow_le_pow_right (by omega : 1 ≤ 4*y) (Nat.le_succ _)).trans hmax)
  have hqWord : (qs (_root_.ThreeSum.LightBandPrimeDepth.depth M y) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hqMax).trans hmaxWord
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 23) (by rfl : program[23]?=some (body 0 1 22))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeCore.body _root_.ThreeSum.LightEncodedColorPrimeCore.time
  have hDepth := (((_root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeDepth.program_meets (d := d+1) (μ := μ) hy hdWord).append
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.program.map (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate 1))).append
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeChain.program.map (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate 4))).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeCore.body 0 1 22]
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hDepth _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hDepth ?_ ?_ ?_ ?_
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
     on_goal -1 => (rintro levels μ₀ ⟨hlevels, hmem⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₀
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.EncodedColorPrimeData.poolBase free : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.EncodedColorPrimeData.poolBase]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.EncodedColorPrimeData.poolBase] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.EncodedColorPrimeData.poolBase] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hPool := ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.meets
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.program_meets (d := d+1) (μ := μ) (y := y) (free := _root_.ThreeSum.EncodedColorPrimeData.poolBase free)
      hw (by omega) hy hpSpace hpWord) _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeDepth.program).append
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeChain.program.map (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate 4))).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeCore.body 0 1 22]
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hPool _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hPool ?_ ?_ ?_ ?_
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
     on_goal -1 => (rintro count μ₁ ⟨hcount, hpool, keepPool⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst count
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.EncodedColorPrimeData.prefixBase free y : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.EncodedColorPrimeData.prefixBase, _root_.ThreeSum.EncodedColorPrimeData.poolBase]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.EncodedColorPrimeData.prefixBase, _root_.ThreeSum.EncodedColorPrimeData.poolBase] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.EncodedColorPrimeData.prefixBase, _root_.ThreeSum.EncodedColorPrimeData.poolBase] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have records₁ : _root_.ThreeSum1960614.Machine.Light.Seg μ₁ recs (_root_.ThreeSum.BandCandidateRows.cells rs) := by
    apply hrecords.congr
    intro i hi
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.cells_length] at hi
    exact keepPool _ (by unfold _root_.ThreeSum.EncodedColorPrimeData.poolBase; omega)
  have valuesA₁ : ∀ i < nA, |μ₁ (a+i)| ≤ (U : ℤ) := by
    intro i hi; rw [keepPool _ (by unfold _root_.ThreeSum.EncodedColorPrimeData.poolBase; omega)]; exact hA i hi
  have valuesB₁ : ∀ i < nB, |μ₁ (b+i)| ≤ (U : ℤ) := by
    intro i hi; rw [keepPool _ (by unfold _root_.ThreeSum.EncodedColorPrimeData.poolBase; omega)]; exact hB i hi
  have valuesC₁ : ∀ i < nC, |μ₁ (c+i)| ≤ (U : ℤ) := by
    intro i hi; rw [keepPool _ (by unfold _root_.ThreeSum.EncodedColorPrimeData.poolBase; omega)]; exact hC i hi
  have hChain := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.meets
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeChain.program_meets (d := d+1) (μ := μ₁) (aux := _root_.ThreeSum.EncodedColorPrimeData.poolBase free) (free := _root_.ThreeSum.EncodedColorPrimeData.prefixBase free y)
      (Y := 4*y) (_root_.ThreeSum.LightPrimePool.prime y) rs hw (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.size_pos hy) hg
      (by unfold _root_.ThreeSum.EncodedColorPrimeData.prefixBase _root_.ThreeSum.EncodedColorPrimeData.poolBase; omega) (by unfold _root_.ThreeSum.EncodedColorPrimeData.prefixBase _root_.ThreeSum.EncodedColorPrimeData.poolBase; omega)
      (by unfold _root_.ThreeSum.EncodedColorPrimeData.prefixBase _root_.ThreeSum.EncodedColorPrimeData.poolBase; omega) (by unfold _root_.ThreeSum.EncodedColorPrimeData.prefixBase _root_.ThreeSum.EncodedColorPrimeData.poolBase; omega)
      (by unfold _root_.ThreeSum.EncodedColorPrimeData.prefixBase; omega) hcSpace hcWord (by omega)
      records₁ hflag hvalid valuesA₁ valuesB₁ valuesC₁
      (fun i hi => hpool.read hi) (fun i hi => (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prime_spec hi).1)
      (fun i hi j hj heq => _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prime_injective hi hj heq)
      (fun i hi => (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prime_spec hi).2.2) hmax) _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeCore.poolProgram).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeCore.body 0 1 22]
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hChain _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hChain ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hlevels]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hlevels] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hlevels] <;> omega)
     on_goal -1 => (rintro result μ₂ ⟨hresult, hprefix, keepChain⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hmod (i : ℕ) : _root_.ThreeSum.BandPrimeChoice.modulus (_root_.ThreeSum.LightPrimePool.prime y) (_root_.ThreeSum.LightPrimePool.size y)
      nA nB nC g (fun j => μ₁ (a+j)) (fun j => μ₁ (b+j)) (fun j => μ₁ (c+j)) rs i=qs i :=
    _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeChoice.modulus_congr rs (fun j hj => keepPool _ (by unfold _root_.ThreeSum.EncodedColorPrimeData.poolBase; omega))
      (fun j hj => keepPool _ (by unfold _root_.ThreeSum.EncodedColorPrimeData.poolBase; omega)) (fun j hj => keepPool _ (by unfold _root_.ThreeSum.EncodedColorPrimeData.poolBase; omega)) i
  have hresult' : result=(qs (_root_.ThreeSum.LightBandPrimeDepth.depth M y) : ℤ) := by rw [hresult,hmod]
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.EncodedColorPrimeData.nextFree free M y : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.EncodedColorPrimeData.nextFree, hlevels]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.EncodedColorPrimeData.nextFree, hlevels] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.EncodedColorPrimeData.nextFree, hlevels] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen free (qs (_root_.ThreeSum.LightBandPrimeDepth.depth M y) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hresult']
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hresult'] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hresult'] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (free + 1) (_root_.ThreeSum.LightBandPrimeDepth.depth M y : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hlevels]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hlevels] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hlevels] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (free + 2) (_root_.ThreeSum.EncodedColorPrimeData.nextFree free M y : ℕ) ?_ ?_ ?_
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (free + 3) (_root_.ThreeSum.EncodedColorPrimeData.poolBase free : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.EncodedColorPrimeData.poolBase]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.EncodedColorPrimeData.poolBase] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.EncodedColorPrimeData.poolBase] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (free + 4) (_root_.ThreeSum.LightPrimePool.size y : ℕ) ?_ ?_ ?_
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (free + 5) (_root_.ThreeSum.EncodedColorPrimeData.prefixBase free y : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.EncodedColorPrimeData.prefixBase, _root_.ThreeSum.EncodedColorPrimeData.poolBase]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.EncodedColorPrimeData.prefixBase, _root_.ThreeSum.EncodedColorPrimeData.poolBase] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.EncodedColorPrimeData.prefixBase, _root_.ThreeSum.EncodedColorPrimeData.poolBase] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (qs (_root_.ThreeSum.LightBandPrimeDepth.depth M y) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hresult']
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hresult'] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hresult'] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  refine ⟨rfl,⟨?_,?_,?_⟩,?_⟩
  · intro i hi
    have hi' : i < 6 := by simpa only [_root_.ThreeSum.EncodedColorPrimeData.values,List.length_cons,List.length_nil] using hi
    interval_cases i <;> simp [_root_.ThreeSum.EncodedColorPrimeData.values,qs]
  · dsimp only
    apply hpool.congr
    intro i hi
    have hi' : i < _root_.ThreeSum.LightPrimePool.size y := by simpa only [_root_.ThreeSum.LightPrimePool.size,List.length_map] using hi
    repeat' rw [Function.update_of_ne (by unfold _root_.ThreeSum.EncodedColorPrimeData.poolBase; omega)]
    exact keepChain _ (by unfold _root_.ThreeSum.EncodedColorPrimeData.prefixBase; omega)
  · intro i hi
    dsimp only
    repeat' rw [Function.update_of_ne (by unfold _root_.ThreeSum.EncodedColorPrimeData.prefixBase _root_.ThreeSum.EncodedColorPrimeData.poolBase; omega)]
    exact (hprefix i hi).trans (congrArg Int.ofNat (hmod i))
  · intro i hi
    dsimp only
    repeat' rw [Function.update_of_ne (by omega)]
    exact (keepChain i (by unfold _root_.ThreeSum.EncodedColorPrimeData.prefixBase _root_.ThreeSum.EncodedColorPrimeData.poolBase; omega)).trans (keepPool i (by unfold _root_.ThreeSum.EncodedColorPrimeData.poolBase; omega))
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeCore.program_meets__implementation_60a0d335c2) := (@ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeCore.program_meets__implementation_60a0d335c2)

#print axioms solution
