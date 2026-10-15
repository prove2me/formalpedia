-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:12:16.512492+00:00
-- url     : https://prove2.me/submissions/a3aa0a1d-a520-4881-98d4-999ffe866f1f

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightColorScanHost_Procs_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightParameterInit_Procs_meets

local instance platformRadixNonzero_7d7643aff4 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.ColorParameters
end ThreeSum.ColorParameters
namespace ThreeSum.EncodedColorResources
end ThreeSum.EncodedColorResources
namespace ThreeSum.LightColorParametersCosts
end ThreeSum.LightColorParametersCosts
namespace ThreeSum.LightColorScanHost
end ThreeSum.LightColorScanHost
namespace ThreeSum.LightParameterInit
end ThreeSum.LightParameterInit
namespace ThreeSum.LightThreeSumColorDriver
end ThreeSum.LightThreeSumColorDriver
namespace ThreeSum.LightThreeSumFastDriver
end ThreeSum.LightThreeSumFastDriver
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.ReportingHostRelocation
end ThreeSum.ReportingHostRelocation
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.ThreeSumColorDriverResources
end ThreeSum.ThreeSumColorDriverResources
namespace ThreeSum.ThreeSumParameterResources
end ThreeSum.ThreeSumParameterResources
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
end ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.ColorParameters
end ThreeSum1960614.Machine.ThreeSum.ColorParameters
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorResources
end ThreeSum1960614.Machine.ThreeSum.EncodedColorResources
namespace ThreeSum1960614.Machine.ThreeSum.LightColorParametersCosts
end ThreeSum1960614.Machine.ThreeSum.LightColorParametersCosts
namespace ThreeSum1960614.Machine.ThreeSum.LightColorScanHost
end ThreeSum1960614.Machine.ThreeSum.LightColorScanHost
namespace ThreeSum1960614.Machine.ThreeSum.LightParameterInit
end ThreeSum1960614.Machine.ThreeSum.LightParameterInit
namespace ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver
end ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver
namespace ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver
end ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
end ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources
end ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources
end ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources
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
# One fixed integer-parameter initializer from the input length

The program starts with only `n`, an output pointer, and a scratch pointer.
It constructs the exact block schedule, local graph counts, selected local
prime, cap, typed global output count, radix, rounded band size, and prime
window. Every helper in the fixed program has an operational contract.
-/

namespace ThreeSum.LightParameterInit
open _root_.ThreeSum.LightParameterInit


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales

set_option maxHeartbeats 1500000
set_option maxRecDepth 5000















variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem program_meets {μ : ℕ → ℤ} {n dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+464*_root_.ThreeSum.LightParameterInit.half n+6 ≤ lim.depth)
    (hout : dst+19 ≤ work) (hspace : _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.space work n ≤ lim.space)
    (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.word n : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.program 0 d [n,dst,work] μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.time n)
      (fun r μ' => r = (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ' dst (_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values n) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' work dst 19) := _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.procs.meets hw hd hout hspace hword

end ThreeSum.LightParameterInit

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

/-! # Load the actual index width and run the entire coloring family -/

namespace ThreeSum.LightColorScanHost
open _root_.ThreeSum.LightColorScanHost


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.ColorParameters
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorParameters
open _root_.ThreeSum.LightColorParametersCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.LightColorParametersCosts

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000







theorem parameters_bits {n params : ℕ} {μ : ℕ → ℤ}
    (H : _root_.ThreeSum1960614.Machine.Light.Seg μ params (_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values n)) : μ params=(_root_.ThreeSum.Scales.inputBits n : ℤ) := by
  have hh := H 0 (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values])
  simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values] using hh



variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}



end ThreeSum.LightColorScanHost

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact polynomial resources for the executed parameter initializer

The nineteen-cell output starts at an arbitrary destination. Scratch begins
immediately after that header; its reservation is translated only once.
-/

namespace ThreeSum.ThreeSumParameterResources
open _root_.ThreeSum.ThreeSumParameterResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.EncodedColorResources
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds

set_option maxHeartbeats 2200000
set_option maxRecDepth 14000



















theorem space_eq (dst n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.space (_root_.ThreeSum.ThreeSumParameterResources.work dst) n=dst+_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources.cells n := by
  unfold _root_.ThreeSum.ThreeSumParameterResources.work _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources.cells _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.space _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.space _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.space
    _root_.ThreeSum.LightSelectedPrime.space _root_.ThreeSum.LightPrimePool.space
  omega





noncomputable section





end

theorem resources_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {n U dst d : ℕ}
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources.need n U).Ok lim dst d) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.space (_root_.ThreeSum.ThreeSumParameterResources.work dst) n ≤ lim.space ∧
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.word n : ℤ) ≤ lim.word ∧
      d+464*_root_.ThreeSum.LightParameterInit.half n+6 ≤ lim.depth := by
  refine ⟨?_,hok.word,?_⟩
  · rw [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources.space_eq]
    exact hok.cells
  · simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources.need,_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources.depth,Nat.add_assoc] using hok.depth

theorem program_meets {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ→ℤ} {n U dst d : ℕ}
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources.need n U).Ok lim dst d) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.program 0 d [n,dst,_root_.ThreeSum.ThreeSumParameterResources.work dst] μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.time n)
      (fun r ν => r=(_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Seg ν dst (_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values n) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν (_root_.ThreeSum.ThreeSumParameterResources.work dst) dst 19) := by
  obtain ⟨hs,hw,hd⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources.resources_of_ok hok
  exact _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.program_meets hok.space hd le_rfl hs hw

theorem kept_of_post {μ ν : ℕ→ℤ} {dst : ℕ} (H : _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν (_root_.ThreeSum.ThreeSumParameterResources.work dst) dst 19) :
    _root_.ThreeSum1960614.Machine.Light.Kept μ ν dst := by
  intro i hi
  exact H i ⟨by unfold _root_.ThreeSum.ThreeSumParameterResources.work; omega,Or.inl hi⟩

end ThreeSum.ThreeSumParameterResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Close the actual color decoder and scan around a concrete color program

The supplied program stays at its original indices. Four actual procedures
are appended: the six-cell decoder, scalar division, recursive short-circuit
scan, and parameter-header reader. The resulting program can then be
relocated by the already verified general relocation theorem.
-/

namespace ThreeSum.LightThreeSumColorDriver
open _root_.ThreeSum.LightThreeSumColorDriver


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.ColorParameters
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorParameters
open _root_.ThreeSum.LightColorParametersCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.LightColorParametersCosts

set_option maxHeartbeats 2000000
set_option maxRecDepth 14000





theorem program_length (colorProgram : _root_.ThreeSum1960614.Machine.Light.Program) (pColor : ℕ) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver.program colorProgram pColor).length=colorProgram.length+4 := by simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver.program,_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver.extra]



theorem program_meets {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {colorProgram : _root_.ThreeSum1960614.Machine.Light.Program} {pColor : ℕ}
    {src n params row colorTime colorDepth d : ℕ} (x : Fin n→ℤ) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hspace : row+6≤lim.space)
    (hsrc : src≤row) (hparams : params<row)
    (hword : (_root_.ThreeSum.LightColorScanHost.word n : ℤ)≤lim.word)
    (hd : d+_root_.ThreeSum.ColorParameters.count (_root_.ThreeSum.LightColorParametersCosts.width n)+colorDepth+4≤lim.depth)
    (hread : μ params=(_root_.ThreeSum.Scales.inputBits n : ℤ))
    (hcolor : ∀ (i : ℕ) (hi : i<_root_.ThreeSum.ColorParameters.count (_root_.ThreeSum.LightColorParametersCosts.width n)) (ν : ℕ→ℤ),
      _root_.ThreeSum1960614.Machine.Light.Kept μ ν row → _root_.ThreeSum1960614.Machine.Light.Seg ν row (_root_.ThreeSum.ColorParameters.fields (_root_.ThreeSum.ColorParameters.parameter hi)) →
      ∀ dd : ℕ, dd+colorDepth≤lim.depth →
      _root_.ThreeSum1960614.Machine.Light.Meets lim colorProgram pColor dd [src,n,params,row,row+6] ν colorTime
        (fun r ξ => (r=0 ∨ r=1) ∧
          (r=1 ↔ _root_.ThreeSum.ColorClassLists.witness (_root_.ThreeSum.ColorParameters.parameter hi) x) ∧ _root_.ThreeSum1960614.Machine.Light.Kept ν ξ row)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver.program colorProgram pColor) (colorProgram.length+3) d
      [src,n,params,row] μ (_root_.ThreeSum.LightColorScanHost.time colorTime n)
      (fun r ξ => (r=0 ∨ r=1) ∧ (r=1 ↔ _root_.ThreeSum.Coloring.DistinctZeroSum x) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ξ row) := by
  apply (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver.procs colorProgram pColor).meets x μ hw hspace hsrc hparams hword hd hread
  intro i hi ν hkeep hrow dd hdepth
  exact (hcolor i hi ν hkeep hrow dd hdepth).append (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver.extra colorProgram pColor)

end ThreeSum.LightThreeSumColorDriver

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Affine resources for a color scan and its single parameter initialization

Per-color storage is reused after one six-cell color row. The full driver
uses nineteen persistent parameter cells and reclaims the initializer's
scratch before the scan. Both allocations have coefficient one on free.
-/

namespace ThreeSum.ThreeSumColorDriverResources
open _root_.ThreeSum.ThreeSumColorDriverResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum.LightColorParametersCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.LightColorParametersCosts
open _root_.ThreeSum.ColorParameters
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorParameters

set_option maxHeartbeats 2000000
set_option maxRecDepth 14000







theorem scan_bounds_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {colorNeed : ℕ→ℕ→_root_.ThreeSum1960614.Machine.Light.Need} {n U row d : ℕ}
    (H : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.need colorNeed n U).Ok lim row d) :
    row+6≤lim.space ∧ (_root_.ThreeSum.LightColorScanHost.word n : ℤ)≤lim.word ∧
      d+_root_.ThreeSum.ColorParameters.count (_root_.ThreeSum.LightColorParametersCosts.width n)+(colorNeed n U).depth+4≤lim.depth := by
  have hs := H.cells
  have hd := H.depth
  dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.need,_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.overhead] at hs hd
  refine ⟨by omega,?_,by omega⟩
  exact (Int.ofNat_le.mpr (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.need,_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.overhead]; omega)).trans H.word

theorem color_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {colorNeed : ℕ→ℕ→_root_.ThreeSum1960614.Machine.Light.Need} {n U row d dd : ℕ}
    (H : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.need colorNeed n U).Ok lim row d)
    (hd : dd+(colorNeed n U).depth≤lim.depth) :
    (colorNeed n U).Ok lim (row+6) dd := by
  have hs := H.cells
  dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.need,_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.overhead] at hs
  exact ⟨(Int.ofNat_le.mpr (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.need,_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.overhead]; omega)).trans H.word,
    by omega,H.space,hd⟩

theorem parameters_of_full_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {colorNeed : ℕ→ℕ→_root_.ThreeSum1960614.Machine.Light.Need} {n U free d : ℕ}
    (H : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.fullNeed colorNeed n U).Ok lim free d) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources.need n U).Ok lim free (d+1) :=
  H.mono (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.fullNeed]; omega) (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.fullNeed]; omega)
    (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.fullNeed]; omega)

theorem scan_of_full_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {colorNeed : ℕ→ℕ→_root_.ThreeSum1960614.Machine.Light.Need} {n U free d : ℕ}
    (H : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.fullNeed colorNeed n U).Ok lim free d) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.need colorNeed n U).Ok lim (free+19) (d+1) :=
  H.mono (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.fullNeed]; omega) (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.fullNeed]; omega)
    (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.fullNeed]; omega)







noncomputable section









end
end ThreeSum.ThreeSumColorDriverResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Run the closed color scan from actual input and parameter arrays -/

namespace ThreeSum.LightThreeSumColorDriver
open _root_.ThreeSum.LightThreeSumColorDriver


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.ColorParameters
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorParameters
open _root_.ThreeSum.LightColorParametersCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.LightColorParametersCosts

set_option maxHeartbeats 1800000
set_option maxRecDepth 14000



theorem parameter_values_length (n : ℕ) : (_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values n).length=19 := rfl

theorem program_meets_bounded {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {colorProgram : _root_.ThreeSum1960614.Machine.Light.Program} {pColor : ℕ}
    {colorNeed : ℕ→ℕ→_root_.ThreeSum1960614.Machine.Light.Need} {src n params row U colorTime d : ℕ}
    (x : Fin n→ℤ) (μ : ℕ→ℤ)
    (H : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.need colorNeed n U).Ok lim row d)
    (hsrc : src+n≤row) (hparams : params+19≤row)
    (hinput : _root_.ThreeSum1960614.Machine.Light.Seg μ src (List.ofFn x)) (hparameters : _root_.ThreeSum1960614.Machine.Light.Seg μ params (_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values n))
    (hcolor : _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver.ColorLaw lim colorProgram pColor colorNeed src n params row U colorTime x) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver.program colorProgram pColor) (colorProgram.length+3) d
      [src,n,params,row] μ (_root_.ThreeSum.LightColorScanHost.time colorTime n)
      (fun r ξ => (r=0 ∨ r=1) ∧ (r=1 ↔ _root_.ThreeSum.Coloring.DistinctZeroSum x) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ξ row) := by
  obtain ⟨hs,hw,hd⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.scan_bounds_of_ok H
  apply _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver.program_meets x μ H.space hs (by omega) (by omega) hw hd
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightColorScanHost.parameters_bits hparameters)
  intro i hi ν hkeep hrow dd hdepth
  exact hcolor (_root_.ThreeSum.ColorParameters.parameter hi) ν dd (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.color_of_ok H hdepth)
    (hinput.of_kept hkeep (by simpa only [List.length_ofFn] using hsrc))
    (hparameters.of_kept hkeep (by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver.parameter_values_length] using hparams)) hrow

end ThreeSum.LightThreeSumColorDriver

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Initialize parameters once and execute the complete color family

The public arguments are [source,n,free]. The nineteen-cell parameter
record starts at free; the reusable six-cell color row starts at free+19;
the concrete selected-color program receives free+25 as its work boundary.
-/

namespace ThreeSum.LightThreeSumFastDriver
open _root_.ThreeSum.LightThreeSumFastDriver


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 2200000
set_option maxRecDepth 18000












theorem libraries_length (colorProgram : _root_.ThreeSum1960614.Machine.Light.Program) (pColor : ℕ) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.libraries colorProgram pColor).length=colorProgram.length+26 := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.libraries,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program,List.length_append,List.length_map,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver.program_length]
  change 22+(colorProgram.length+4)=colorProgram.length+26
  omega



theorem main_lookup (colorProgram : _root_.ThreeSum1960614.Machine.Light.Program) (pColor : ℕ) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.program colorProgram pColor)[colorProgram.length+26]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.body (colorProgram.length+25)) := by
  have hh : (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.libraries colorProgram pColor++[_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.body (colorProgram.length+25)])[(_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.libraries colorProgram pColor).length+0]?=
      some (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.body (colorProgram.length+25)) := by
    apply _root_.ThreeSum1960614.Machine.Light.getElem?_append_length_add
    rfl
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.program,_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.libraries_length,Nat.add_zero] using hh





end ThreeSum.LightThreeSumFastDriver

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightThreeSumFastDriver
open _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 2200000
set_option maxRecDepth 18000
section

theorem ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.program_meets__implementation_4553360059 {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {colorProgram : _root_.ThreeSum1960614.Machine.Light.Program} {pColor : ℕ}
    {colorNeed : ℕ→ℕ→_root_.ThreeSum1960614.Machine.Light.Need} {src n free U colorTime d : ℕ}
    (x : Fin n→ℤ) (μ : ℕ→ℤ)
    (H : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.fullNeed colorNeed n U).Ok lim free d)
    (hsrc : src+n≤free) (hinput : _root_.ThreeSum1960614.Machine.Light.Seg μ src (List.ofFn x))
    (hcolor : _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver.ColorLaw lim colorProgram pColor colorNeed
      src n free (_root_.ThreeSum.LightThreeSumFastDriver.row free) U colorTime x) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.program colorProgram pColor) (colorProgram.length+26) d [src,n,free] μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.time colorTime n)
      (fun r ξ => (r=0 ∨ r=1) ∧ (r=1 ↔ _root_.ThreeSum.Coloring.DistinctZeroSum x) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ξ free) := by
  have hinitOk := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.parameters_of_full_ok H
  have hscanOk := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.scan_of_full_ok H
  have hspace := (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverResources.scan_bounds_of_ok hscanOk).1
  have hw := H.space
  have hd := (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources.resources_of_ok hinitOk).2.2
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.main_lookup colorProgram pColor)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.body _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightThreeSumFastDriver.row free : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightThreeSumFastDriver.row]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightThreeSumFastDriver.row] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightThreeSumFastDriver.row] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hinit := (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources.program_meets (μ := μ) hinitOk).append
    ((_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver.program colorProgram pColor).map
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.program.length)++[_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.body (colorProgram.length+25)])
  change _root_.ThreeSum1960614.Machine.Light.Meets lim (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.program colorProgram pColor) 0 (d+1) _ μ _ _ at hinit
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hinit _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hinit ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.ThreeSumParameterResources.work, _root_.ThreeSum.LightThreeSumFastDriver.row]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.ThreeSumParameterResources.work, _root_.ThreeSum.LightThreeSumFastDriver.row] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.ThreeSumParameterResources.work, _root_.ThreeSum.LightThreeSumFastDriver.row] <;> omega)
     on_goal -1 => (rintro modulus ν ⟨_, hparams, hkeptInit⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hkeep := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources.kept_of_post hkeptInit
  have hread := hinput.of_kept hkeep (by simpa only [List.length_ofFn] using hsrc)
  have hscan := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver.program_meets_bounded x ν hscanOk
    (by omega) (by omega) hread hparams hcolor
  have hscanRun := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.meets hscan _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.program).append
    [_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.body (colorProgram.length+25)]
  have hentry : _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.program.length+(colorProgram.length+3)=colorProgram.length+25 := by
    change 22+(colorProgram.length+3)=colorProgram.length+25
    omega
  rw [hentry] at hscanRun
  change _root_.ThreeSum1960614.Machine.Light.Meets lim (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.program colorProgram pColor) (colorProgram.length+25) (d+1) _ ν _ _ at hscanRun
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hscanRun _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hscanRun ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightThreeSumFastDriver.row]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightThreeSumFastDriver.row] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightThreeSumFastDriver.row] <;> omega)
     on_goal -1 => (rintro result ξ ⟨hbool, hresult, hkeptScan⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  exact ⟨hbool,hresult,fun a ha => (hkeptScan a (by omega)).trans (hkeep a ha)⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.program_meets__implementation_4553360059) := (@ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.program_meets__implementation_4553360059)

#print axioms solution
