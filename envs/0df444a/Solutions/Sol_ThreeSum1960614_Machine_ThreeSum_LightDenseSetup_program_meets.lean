-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:52:15.187986+00:00
-- url     : https://prove2.me/submissions/651fc7cb-f9cd-485d-ad42-f11be63b6559

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
import Definitions.Def_ThreeSum1962Source_Bundle14
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandWeightedScore_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightCoverKeyData_Stored_of_kept
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightNatPower_meets
import Theorems.Thm_ThreeSum_BandRawA_mem_aIndices_iff_owner
import Theorems.Thm_ThreeSum_BandRawA_mem_allProducts
import Theorems.Thm_ThreeSum_BandRawA_owner_weightedFalseCount
import Theorems.Thm_ThreeSum_BandWeightedScore_block_bound

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BandWeightedScore
end ThreeSum.BandWeightedScore
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightCoverKeyData
end ThreeSum.LightCoverKeyData
namespace ThreeSum.LightDenseCap
end ThreeSum.LightDenseCap
namespace ThreeSum.LightDenseSetup
end ThreeSum.LightDenseSetup
namespace ThreeSum.LightLocalCoverRetention
end ThreeSum.LightLocalCoverRetention
namespace ThreeSum.LightNatPower
end ThreeSum.LightNatPower
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.ReportingHostRelocation
end ThreeSum.ReportingHostRelocation
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
end ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
namespace ThreeSum1960614.Machine.ThreeSum.BandRawA
end ThreeSum1960614.Machine.ThreeSum.BandRawA
namespace ThreeSum1960614.Machine.ThreeSum.BandWeightedScore
end ThreeSum1960614.Machine.ThreeSum.BandWeightedScore
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
end ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData
end ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData
namespace ThreeSum1960614.Machine.ThreeSum.LightDenseCap
end ThreeSum1960614.Machine.ThreeSum.LightDenseCap
namespace ThreeSum1960614.Machine.ThreeSum.LightDenseSetup
end ThreeSum1960614.Machine.ThreeSum.LightDenseSetup
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
namespace ThreeSum1960614.Machine.ThreeSum.LightNatPower
end ThreeSum1960614.Machine.ThreeSum.LightNatPower
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
end ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation

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























theorem partialScore_bound (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) (k : ℕ)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j) :
    _root_.ThreeSum.BandWeightedScore.partialScore primes s q nA nB nC g A B C rs k ≤ k*(s*g^3) := by
  calc
    _ ≤ ∑ _i ∈ range k, s*g^3 := sum_le_sum fun i _ => _root_.ThreeSum.BandWeightedScore.block_bound primes s q nA nB nC g A B C _ hprime hinj
    _ = _ := by simp

theorem score_bound (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j) :
    _root_.ThreeSum.BandWeightedScore.score primes s q nA nB nC g A B C rs ≤ rs.length*(s*g^3) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.partialScore_bound primes s q nA nB nC g A B C rs rs.length hprime hinj









end ThreeSum.BandWeightedScore

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Scalar integer powers in the benchmark language

The exponent is a size parameter, so a loop of that many multiplications
has polynomial-logarithmic cost in the applications below. No power table
or auxiliary memory is required.
-/

namespace ThreeSum.LightNatPower
open _root_.ThreeSum.LightNatPower


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem bounded_meets {p b e : ℕ} (hp : P[p]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.body) (μ : ℕ → ℤ)
    (he : (e : ℤ) ≤ lim.word)
    (hword : (((b+1)^(e+1) : ℕ) : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [b,e] μ (_root_.ThreeSum.LightNatPower.time e)
      (fun r μ' => r = ((b^e : ℕ) : ℤ) ∧ μ' = μ) := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.meets hp μ he
  intro i hi
  have hbase := Nat.pow_le_pow_left (show b ≤ b+1 by omega) i
  have hexp : (b+1)^i ≤ (b+1)^(e+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hz : ((b^i : ℕ) : ℤ) ≤ (((b+1)^(e+1) : ℕ) : ℤ) := by
    exact_mod_cast hbase.trans hexp
  exact hz.trans hword





end ThreeSum.LightNatPower

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
# Each physical A incidence retains exactly its owner's B/C product

The products in this file are mathematical counting domains. The actual
catalog is still constructed by the verified quadratic owner loop and
linear band copies. Distinct owner products are disjoint because their
physical A incidence indices differ, even when their values coincide.
-/

namespace ThreeSum.BandRawA
open _root_.ThreeSum.BandRawA


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.Finset
open scoped _root_.BigOperators

set_option maxHeartbeats 1900000
set_option maxRecDepth 8000



















theorem mem_ownerProduct {nA nB nC g s : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record} {t : ℕ × ℕ × ℕ}
    (hs : s < rs.length) :
    t ∈ _root_.ThreeSum.BandRawA.ownerProduct nA nB nC g rs s ↔
      t.1 < (_root_.ThreeSum.BandRawA.items nA g rs).length ∧ (_root_.ThreeSum.BandRawA.labelAt nA g rs t.1).owner=s ∧
        t.2.1 ∈ _root_.ThreeSum.BandRawA.bandPositions nB g (rs.getD s default).b ∧
        t.2.2 ∈ _root_.ThreeSum.BandRawA.bandPositions nC g (rs.getD s default).c := by
  simp only [_root_.ThreeSum.BandRawA.ownerProduct,mem_product,_root_.ThreeSum.BandRawA.mem_aIndices_iff_owner hs,and_assoc]

theorem ownerProduct_disjoint {nA nB nC g s t : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record}
    (hs : s < rs.length) (ht : t < rs.length) (hst : s ≠ t) :
    Disjoint (_root_.ThreeSum.BandRawA.ownerProduct nA nB nC g rs s) (_root_.ThreeSum.BandRawA.ownerProduct nA nB nC g rs t) := by
  apply disjoint_left.mpr
  intro x hx hy
  have hs' := (_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.mem_ownerProduct hs).mp hx
  have ht' := (_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.mem_ownerProduct ht).mp hy
  exact hst (hs'.2.1.symm.trans ht'.2.1)









theorem sum_allProducts (F : (ℕ × ℕ × ℕ) → ℕ) (nA nB nC g : ℕ)
    (rs : List _root_.ThreeSum.BandCandidateRows.Record) :
    (∑ t ∈ _root_.ThreeSum.BandRawA.allProducts nA nB nC g rs, F t)=
      ∑ s ∈ range rs.length, ∑ t ∈ _root_.ThreeSum.BandRawA.ownerProduct nA nB nC g rs s, F t := by
  unfold _root_.ThreeSum.BandRawA.allProducts
  apply sum_biUnion
  intro s hs t ht hst
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.ownerProduct_disjoint (mem_range.mp hs) (mem_range.mp ht) hst



end ThreeSum.BandRawA

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
# The aggregate prime score is the exact physical incidence-product score

The executable A catalog supplies the first-coordinate values. Its owner
metadata supplies the B/C slices. Thus the mathematical score summed by
the actual prime selector counts this same domain with all multiplicities.
-/

namespace ThreeSum.BandRawA
open _root_.ThreeSum.BandRawA


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.Finset
open scoped _root_.BigOperators

set_option maxHeartbeats 1900000
set_option maxRecDepth 8000







theorem all_weightedFalseCount (primes : ℕ → ℕ) (aux q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) :
    _root_.ThreeSum.Arithmetic.weightedFalseCount (_root_.ThreeSum.BandRawA.allProducts nA nB nC g rs)
      (_root_.ThreeSum.ModuloCounts.difference (_root_.ThreeSum.BandRawA.valueAt nA g rs A) B C)
      (_root_.ThreeSum.Auxiliary.moduli (_root_.ThreeSum.WeightedScore.auxiliarySet primes aux)) q=
      _root_.ThreeSum.BandWeightedScore.score primes aux q nA nB nC g A B C rs := by
  unfold _root_.ThreeSum.Arithmetic.weightedFalseCount
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.sum_allProducts]
  unfold _root_.ThreeSum.BandWeightedScore.score _root_.ThreeSum.BandWeightedScore.partialScore
  apply sum_congr rfl
  intro s hs
  exact _root_.ThreeSum.BandRawA.owner_weightedFalseCount primes aux q nA nB nC g A B C rs (mem_range.mp hs)













end ThreeSum.BandRawA

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

/-!
# Bounded finite index types for the same physical owner products

The A type is the complete flattened incidence array; B and C are the
retained sorted arrays. Coordinate transport is injective and preserves
both each owner's product and its exact weighted collision score.
-/

namespace ThreeSum.BandRawA
open _root_.ThreeSum.BandRawA


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.Finset
open scoped _root_.BigOperators

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000











theorem coordinates_injective {a b c : ℕ} :
    Function.Injective (@_root_.ThreeSum.BandRawA.coordinates a b c) := by
  rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ he
  simp only [_root_.ThreeSum.BandRawA.coordinates,Prod.mk.injEq] at he
  exact Prod.ext (Fin.ext he.1) (Prod.ext (Fin.ext he.2.1) (Fin.ext he.2.2))







@[simp] theorem mem_finiteAllProducts {nA nB nC g : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record}
    {t : Fin (_root_.ThreeSum.BandRawA.items nA g rs).length × Fin nB × Fin nC} :
    t ∈ _root_.ThreeSum.BandRawA.finiteAllProducts nA nB nC g rs ↔
      _root_.ThreeSum.BandRawA.coordinates t ∈ _root_.ThreeSum.BandRawA.allProducts nA nB nC g rs := by
  simp only [_root_.ThreeSum.BandRawA.finiteAllProducts,mem_filter,mem_univ,true_and]





theorem allProducts_bounds {nA nB nC g : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ _root_.ThreeSum.BandRawA.allProducts nA nB nC g rs) :
    t.1 < (_root_.ThreeSum.BandRawA.items nA g rs).length ∧ t.2.1 < nB ∧ t.2.2 < nC := by
  obtain ⟨ha,hb,hc⟩ := _root_.ThreeSum.BandRawA.mem_allProducts.mp ht
  exact ⟨ha,_root_.ThreeSum.BandRawA.bandPositions_lt hb,_root_.ThreeSum.BandRawA.bandPositions_lt hc⟩



theorem finite_lift {nA nB nC g : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ _root_.ThreeSum.BandRawA.allProducts nA nB nC g rs) :
    ∃ u ∈ _root_.ThreeSum.BandRawA.finiteAllProducts nA nB nC g rs, _root_.ThreeSum.BandRawA.coordinates u=t := by
  obtain ⟨ha,hb,hc⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.allProducts_bounds ht
  refine ⟨(⟨t.1,ha⟩,⟨t.2.1,hb⟩,⟨t.2.2,hc⟩),?_,rfl⟩
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.mem_finiteAllProducts.mpr ht



theorem sum_finiteAllProducts (F : (ℕ × ℕ × ℕ) → ℕ) (nA nB nC g : ℕ)
    (rs : List _root_.ThreeSum.BandCandidateRows.Record) :
    (∑ u ∈ _root_.ThreeSum.BandRawA.finiteAllProducts nA nB nC g rs, F (_root_.ThreeSum.BandRawA.coordinates u))=
      ∑ t ∈ _root_.ThreeSum.BandRawA.allProducts nA nB nC g rs, F t := by
  refine sum_bij (fun u _ => _root_.ThreeSum.BandRawA.coordinates u) ?_ ?_ ?_ ?_
  · intro u hu
    exact _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.mem_finiteAllProducts.mp hu
  · intro u hu v hv he
    exact _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.coordinates_injective he
  · intro t ht
    obtain ⟨u,hu,he⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.finite_lift ht
    exact ⟨u,hu,he⟩
  · intro u hu
    rfl



theorem finiteAll_weightedFalseCount (primes : ℕ → ℕ) (aux q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) :
    _root_.ThreeSum.Arithmetic.weightedFalseCount (_root_.ThreeSum.BandRawA.finiteAllProducts nA nB nC g rs)
      (fun t => C t.2.2.val-B t.2.1.val-_root_.ThreeSum.BandRawA.valueAt nA g rs A t.1.val)
      (_root_.ThreeSum.Auxiliary.moduli (_root_.ThreeSum.WeightedScore.auxiliarySet primes aux)) q=
      _root_.ThreeSum.BandWeightedScore.score primes aux q nA nB nC g A B C rs := by
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.all_weightedFalseCount primes aux q nA nB nC g A B C rs]
  unfold _root_.ThreeSum.Arithmetic.weightedFalseCount
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.sum_finiteAllProducts
    (fun t => if (q : ℤ) ∣ _root_.ThreeSum.ModuloCounts.difference (_root_.ThreeSum.BandRawA.valueAt nA g rs A) B C t then
      _root_.ThreeSum.Arithmetic.missWeight (_root_.ThreeSum.Auxiliary.moduli (_root_.ThreeSum.WeightedScore.auxiliarySet primes aux))
        (_root_.ThreeSum.ModuloCounts.difference (_root_.ThreeSum.BandRawA.valueAt nA g rs A) B C t) else 0) nA nB nC g rs





end ThreeSum.BandRawA

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Compute the representation cap from the actual retained cover

The two factors are read from the verified cover header. An actual scalar
power loop computes the J-fold cap; no cap value is supplied as an input.
-/

namespace ThreeSum.LightDenseCap
open _root_.ThreeSum.LightDenseCap


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds









theorem header_cap {μ : ℕ → ℤ} {free h J : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.Stored μ free h J) : μ (free+7)=(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h : ℤ) := by
  have hv := H.header 7 (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.values])
  simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.values] using hv

theorem header_schedule {μ : ℕ → ℤ} {free h J : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.Stored μ free h J) : μ (free+10)=(_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h : ℤ) := by
  have hv := H.header 10 (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.values])
  simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.values] using hv



variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {μ : ℕ → ℤ} {free h J d : ℕ}

theorem meets {pMain pPower : ℕ} (hp : P[pMain]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.body pPower))
    (hPower : P[pPower]?=some _root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.body)
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : free+11 ≤ lim.space)
    (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.word h J : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.Stored μ free h J) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [free,J] μ (_root_.ThreeSum.LightDenseCap.time J)
      (fun result ν => result=(_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J : ℤ) ∧ ν=μ) := by
  have budget (a : ℕ) (ha : a ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.word h J) : (a : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ha).trans hword
  have hcap := budget (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.word; omega)
  have hsq := budget (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h^2) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.word; omega)
  have hS := budget (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.word; omega)
  have hb := budget (_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.base h) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.word; omega)
  have hJ := budget J (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.word; omega)
  have hpow := budget ((_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.base h+1)^(J+1)) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.word; omega)
  have hsqZ : (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h : ℤ)*(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h : ℤ) ≤ lim.word := by
    simpa only [Nat.cast_pow,pow_two,Nat.cast_mul] using hsq
  have hbZ : (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h : ℤ)*(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h : ℤ)^2 ≤ lim.word := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.base,Nat.cast_mul,Nat.cast_pow] using hb
  have hsqN : (0 : ℤ) ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h : ℤ)*(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h : ℤ) := by positivity
  have hbN : (0 : ℤ) ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h : ℤ)*(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h : ℤ)^2 := by positivity
  have hcapRead : μ (((free : ℤ)+7).toNat)=(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h : ℤ) := by
    rw [show ((free : ℤ)+7).toNat=free+7 by omega]
    exact _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.header_cap H
  have hSRead : μ (((free : ℤ)+10).toNat)=(_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h : ℤ) := by
    rw [show ((free : ℤ)+10).toNat=free+10 by omega]
    exact _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.header_schedule H
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hp
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.body _root_.ThreeSum.LightDenseCap.time
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
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcapRead]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hcapRead] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcapRead] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hSRead]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hSRead] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hSRead] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h ^ 2 : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, pow_two]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [pow_two] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, pow_two] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.base h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.base]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.base] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.base] <;> omega)
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
     first
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.bounded_meets (d := d + 1) hPower μ hJ hpow) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.bounded_meets (d := d + 1) hPower μ hJ hpow) ?_ ?_ ?_ ?_
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
     on_goal -1 => (rintro result ν ⟨hr, hν⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  exact ⟨hr,hν⟩



theorem program_meets (hw : (lim.space : ℤ) ≤ lim.word) (hspace : free+11 ≤ lim.space)
    (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.word h J : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.Stored μ free h J) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.program 0 d [free,J] μ (_root_.ThreeSum.LightDenseCap.time J)
      (fun result ν => result=(_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J : ℤ) ∧ ν=μ) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.meets rfl rfl hw hspace hword hd H

end ThreeSum.LightDenseCap

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Construct the dense-stop threshold from actual cover and source records

The host computes the representation cap, recomputes the exact aggregate
weighted score at the selected common modulus, multiplies the two, and
initializes the running counter. The four retained cells are counter,
threshold, representation cap and weighted score. Scratch starts after them.
-/

namespace ThreeSum.LightDenseSetup
open _root_.ThreeSum.LightDenseSetup


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

















theorem falseScore_eq (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) :
    _root_.ThreeSum.LightDenseSetup.falseScore primes s q nA nB nC g A B C rs=
      _root_.ThreeSum.BandWeightedScore.score primes s q nA nB nC g A B C rs :=
  _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.finiteAll_weightedFalseCount primes s q nA nB nC g A B C rs

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs q aux s cover free maxMod U h J : ℕ}



end ThreeSum.LightDenseSetup

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightDenseSetup
open _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetup

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs q aux s cover free maxMod U h J : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.program_meets__implementation_098fb4a064 (primes : ℕ → ℕ) (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+Nat.clog 2 maxMod+7 ≤ lim.depth)
    (hg : 0 < g) (hq : 0 < q) (hqmax : q ≤ maxMod)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hrecs : recs+4*rs.length ≤ free) (haux : aux+s ≤ free)
    (hcover : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd cover h J ≤ free)
    (hspace : _root_.ThreeSum.LightWeightedScore.space (free+4) maxMod g U ≤ lim.space)
    (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.word maxMod nA nB nC g rs.length s U h J : ℤ) ≤ lim.word)
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.Stored μ cover h J)
    (hrecords : _root_.ThreeSum1960614.Machine.Light.Seg μ recs (_root_.ThreeSum.BandCandidateRows.cells rs))
    (hflag : ∀ r ∈ rs, r.flag=0 ∨ r.flag=1)
    (hvalid : ∀ r ∈ rs, r.flag=1 → r.a*g ≤ nA ∧ r.b*g ≤ nB ∧ r.c*g ≤ nC)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ))
    (hread : ∀ i < s, μ (aux+i)=(primes i : ℤ))
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j)
    (hproduct : ∀ i < s, q*primes i ≤ maxMod) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.program 19 d [a,b,c,nA,nB,nC,g,recs,rs.length,q,aux,s,cover,J,free] μ
      (_root_.ThreeSum.LightDenseSetup.time maxMod g rs.length s U J)
      (fun result ν => result=(free : ℤ) ∧
        _root_.ThreeSum.LightDenseSetup.Stored ν free (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J)
          (_root_.ThreeSum.LightDenseSetup.falseScore primes s q nA nB nC g
            (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) rs) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.Stored ν cover h J ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν free) := by
  let score := _root_.ThreeSum.BandWeightedScore.score primes s q nA nB nC g
    (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) rs
  have budget (x : ℕ) (hx : x ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.word maxMod nA nB nC g rs.length s U h J) :
      (x : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hx).trans hword
  have hcapWord := budget (_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.word h J) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.word; omega)
  have hscoreWord := budget (_root_.ThreeSum.LightBandWeightedScore.word maxMod nA nB nC g rs.length s U)
    (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.word; omega)
  have hcapFit := budget (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.word; omega)
  have hsBound : score ≤ rs.length*(s*g^3) :=
    _root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.score_bound primes s q nA nB nC g _ _ _ rs hprime hinj
  have hthresholdFit : ((_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J*score : ℕ) : ℤ) ≤ lim.word := by
    apply budget
    exact (Nat.mul_le_mul_left _ hsBound).trans (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.word; omega)
  have hthresholdZ : (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J : ℤ)*(score : ℤ) ≤ lim.word := by
    simpa only [Nat.cast_mul] using hthresholdFit
  have hthresholdN : (0 : ℤ) ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J : ℤ)*(score : ℤ) := by positivity
  have hscoreFit : (score : ℤ) ≤ lim.word := by
    apply budget
    apply hsBound.trans
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.word _root_.ThreeSum.LightBandWeightedScore.word
    omega
  have hfree : free+4 ≤ lim.space := by
    have hh := (le_max_right _ _).trans hspace
    change free+4+(Nat.log 2 (maxMod+1)+2) ≤ lim.space at hh
    omega
  have hcoverBase := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRetention.base_le_nextFree (_root_.ThreeSum.LightLocalCoverInit.base cover) h
  change cover+20 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.afterCover cover h at hcoverBase
  have hcoverNext := _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.afterCover_le_keyEnd cover h J
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 19) (by rfl : program[19]?=some (body 0 18))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.body _root_.ThreeSum.LightDenseSetup.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (free + 4 : ℕ) ?_ ?_ ?_
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
  have hcapCall := ((_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.program_meets (d := d+1) (μ := μ)
    hw (by omega) hcapWord (by omega) H).append
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandWeightedScore.program.map (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate 2))).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.body 0 18]
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hcapCall _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hcapCall ?_ ?_ ?_ ?_
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
     on_goal -1 => (rintro cap μ₁ ⟨hcap, hμ₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₁
  have hscoreCall := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.meets
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandWeightedScore.program_meets (d := d+1) (μ := μ) (free := free+4)
      primes rs hw (by omega) hg hq hqmax (by omega) (by omega) (by omega)
      (by omega) (by omega) hspace hscoreWord hrecords hflag hvalid hA hB hC
      hread hprime hinj hproduct) _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.program).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.body 0 18]
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hscoreCall _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hscoreCall ?_ ?_ ?_ ?_
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
     on_goal -1 => (rintro total μ₂ ⟨hscore, hkeep⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have htotal : total=(score : ℤ) := hscore
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J * score : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcap, htotal]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hcap, htotal] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcap, htotal] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen free (0 : ℕ) ?_ ?_ ?_
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (free + 1) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J * score : ℕ) ?_ ?_ ?_
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (free + 2) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcap]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hcap] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcap] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (free + 3) (score : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, htotal]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [htotal] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, htotal] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (free : ℕ) ?_ ?_ ?_
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
  refine ⟨rfl,?_,?_,?_⟩
  · exact ⟨by simp,by simp [score,_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.falseScore_eq],by simp,by simp [score,_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.falseScore_eq]⟩
  · apply H.of_kept
    intro i hi
    change Function.update (Function.update (Function.update (Function.update μ₂ free _)
      (free+1) _) (free+2) _) (free+3) _ i=μ i
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),
      Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    exact hkeep i (by omega)
  · intro i hi
    change Function.update (Function.update (Function.update (Function.update μ₂ free _)
      (free+1) _) (free+2) _) (free+3) _ i=μ i
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),
      Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    exact hkeep i (by omega)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.program_meets__implementation_098fb4a064) := (@ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.program_meets__implementation_098fb4a064)

#print axioms solution
